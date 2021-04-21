//! RSA keys.
//!
//! We follow [ham20][1]. In particular, our private keys consist
//! of (p, q, f = dp = e.modulo(p).inverse(), g = dq = e.modulo(q).inverse()),
//! we don't need `d`, neither store nor calculate `q^{-1}`,
//! and restrict `e` to 65537.
//!
//!
//! [1]: https://eprint.iacr.org/2020/1507

use rand_core::{CryptoRng, RngCore};
use zeroize::Zeroize;

use crate::{Convenient, Digit, Error, F4, Long, Odd, PrimeModular, Short, ShortPrime, Result};
use crate::numbers::{Bits, NumberMut};
use crate::padding::{EncryptionPadding, SignaturePadding, Unpadded};

/// RSA public key.
///
/// Here, `N = pq` is the product of the private pair of primes.
/// `e` is fixed to be 65537 = 0x10001.
#[allow(non_snake_case)]
#[derive(Zeroize)]
pub struct PublicKey<const D: usize> {
    pub N: Convenient<D, D>,
}

impl<const D: usize> Bits for PublicKey<D> {
    const BITS: usize = <Long<D> as Bits>::BITS;
}

impl<const D: usize> PublicKey<D> {
    /// [RSAEP][rsaep]
    ///
    /// [rsaep]: https://tools.ietf.org/html/rfc8017#section-5.1.1
    pub fn encryption_primitive(&self, msg: &[u8]) -> Result<Long<D>> {

        // 1.
        if msg.len()*8 > Self::BITS {
            return Err(Error);
        }
        let m = Long::<D>::from_bytes(msg);

        if m  >= *self.N.as_unsigned() {
            return Err(Error);
        }

        let c = m.modulo(&self.N).power(&F4::SHORT).canonical_lift();
        Ok(c)
    }

    /// [RSAVP1][rsavp]
    ///
    /// [rsavp]: https://tools.ietf.org/html/rfc8017#section-5.2.2
    pub fn verification_primitive(&self, signature: &[u8]) -> Result<Long<D>> {
        self.encryption_primitive(signature)
    }

    /// Encrypt a plaintext with respect to a padding method.
    pub fn encrypt<P, R>(&self, plaintext: &[u8], _: P, rng: R) -> Result<Long<D>>
    where
        P: EncryptionPadding<D>,
        R: CryptoRng + RngCore,
    {
        let padded = P::pad(plaintext, rng).map_err(|_| Error)?;
        self.encryption_primitive(&padded.to_bytes())
    }

    /// Verify a signature with respect to a padding method.
    // pub fn verify<P, R>(&self, msg: &[u8], signature: &Long<D>, _: P) -> Result<()>
    pub fn verify<P>(&self, msg: &[u8], signature: &[u8], _: P) -> Result<()>
    where
        P: SignaturePadding<D>,
    {
        // let verifier = self.verification_primitive(&signature.to_bytes())?;
        let verifier = self.verification_primitive(signature)?;
        P::verify(msg, &verifier).map_err(|_| Error)
    }

}

impl<const D: usize> PrivateKey<D> {
    fn q_inv_mod_p(&self) -> PrimeModular<'_, D, 0> {
        PrimeModular { x: self.precomputed.q_inv.clone(), p: &self.p }
    }

    pub fn decryption_primitive(&self, ciphertext: &[u8]) -> Result<Long<D>> {
        self.inversion_free_decryption(ciphertext)
    }

    /// [RSADP][rsadp]
    ///
    /// [rsadp]: https://tools.ietf.org/html/rfc8017#section-5.1.2
    pub fn classic_decryption_primitive(&self, ciphertext: &[u8]) -> Result<Long<D>> {

        // 1.
        if ciphertext.len()*8 > Self::BITS {
            return Err(Error);
        }
        let c = Long::<D>::from_bytes(ciphertext);

        if c  >= *self.public_key.N.as_unsigned() {
            return Err(Error);
        }

        // 2.a.i.
        let mp = c.modulo_prime(&self.p).power(&self.precomputed.dp);//.canonical_lift();
        let long_mq: Long<D> = c.modulo_prime(&self.q).power(&self.precomputed.dq).canonical_lift().to_unsigned().unwrap();

        // 2.a.iii.
        let h: Long<D> = (&(&mp - &long_mq.modulo_prime(&self.p)) * &self.q_inv_mod_p()).canonical_lift().to_unsigned().unwrap();


        // 2.a.iv.
        let long_q: Long<D> = self.q.as_unsigned().to_unsigned().unwrap();
        // these wrapping adds and products are all actually not wrapping, as m is "big enough"
        // TODO: orly? otherwise reduce modulo n
        let m: Long<D> = long_mq.wrapping_add(&long_q.wrapping_mul(&h));

        Ok(m)
    }

    /// This saves calculating and storing the inverse $q^{-1}\text{ mod }p$.
    ///
    /// [Source][rsa-improvements]
    ///
    /// [rsa-improvements]: https://eprint.iacr.org/2020/1507.pdf#page=13
    pub fn inversion_free_decryption(&self, ciphertext: &[u8]) -> Result<Long<D>> {

        if ciphertext.len()*8 > Self::BITS {
            return Err(Error);
        }

        let c = Long::<D>::from_bytes(ciphertext);
        if c  >= *self.public_key.N.as_unsigned() {
            return Err(Error);
        }

        let mp = c.modulo_prime(&self.p).to_montgomery().power(&self.precomputed.dp);
        let xp = mp.power(&F4::SHORT);
        let yp = self.q.modulo_prime(&self.p).to_montgomery();
        let alphap = (&xp * &yp).power(&F4::minus_one());
        let betap = (&alphap * &yp).power(&self.p.wrapping_sub(&Short::<D>::from(1)).wrapping_sub(&self.precomputed.dp));
        let mpq_ = (&betap * &xp).to_modular();
        let mpq = mpq_.residue();

        let mq = c.modulo_prime(&self.q).to_montgomery().power(&self.precomputed.dq);
        let xq = mq.power(&F4::SHORT);
        let yq = self.p.modulo_prime(&self.q).to_montgomery();
        let alphaq = (&xq * &yq).power(&F4::minus_one());
        let betaq = (&alphaq * &yq).power(&self.q.wrapping_sub(&Short::<D>::from(1)).wrapping_sub(&self.precomputed.dq));
        let mqp_ = (&betaq * &xq).to_modular();
        let mqp = mqp_.residue();

        let plaintext = (
            &(mpq * self.q.as_unsigned()).to_unsigned::<D, D>().unwrap().modulo(&self.public_key.N)
            +
            &(mqp * self.p.as_unsigned()).to_unsigned::<D, D>().unwrap().modulo(&self.public_key.N)
        ).canonical_lift();

        Ok(plaintext)
    }

    /// As also explained in [Improvements...][rsa-improvements],
    /// it is easy to blind the factors.
    ///
    /// [rsa-improvements]: https://eprint.iacr.org/2020/1507.pdf#page=14
    pub fn blinded_inversion_free_decryption(&self, rng: impl rand_core::CryptoRng + rand_core::RngCore, ciphertext: &[u8])
        -> Result<Long<D>> {

        if ciphertext.len()*8 > Self::BITS {
            return Err(Error);
        }

        let c = Long::<D>::from_bytes(ciphertext);
        if c  >= *self.public_key.N.as_unsigned() {
            return Err(Error);
        }

        let r = Short::<D>::random(rng);

        let mp = c.modulo_prime(&self.p).to_montgomery().power(&self.precomputed.dp);
        let xp = mp.power(&F4::SHORT);
        let yp = (self.q.as_unsigned() * &r).to_unsigned::<D, D>().unwrap().modulo_prime(&self.p).to_montgomery();
        let alphap = (&xp * &yp).power(&F4::minus_one());
        let betap = (&alphap * &yp).power(&self.p.wrapping_sub(&Short::<D>::from(1)).wrapping_sub(&self.precomputed.dp));
        let mpq_ = (&betap * &xp).to_modular();
        let mpq = mpq_.residue();

        let mq = c.modulo_prime(&self.q).to_montgomery().power(&self.precomputed.dq);
        let xq = mq.power(&F4::SHORT);
        let yq = (self.p.as_unsigned() * &r).to_unsigned::<D, D>().unwrap().modulo_prime(&self.q).to_montgomery();
        let alphaq = (&xq * &yq).power(&F4::minus_one());
        let betaq = (&alphaq * &yq).power(&self.q.wrapping_sub(&Short::<D>::from(1)).wrapping_sub(&self.precomputed.dq));
        let mqp_ = (&betaq * &xq).to_modular();
        let mqp = mqp_.residue();

        let plaintext_divided_by_r =
            &(mpq * self.q.as_unsigned()).to_unsigned::<D, D>().unwrap().modulo(&self.public_key.N)
            +
            &(mqp * self.p.as_unsigned()).to_unsigned::<D, D>().unwrap().modulo(&self.public_key.N)
        ;

        let plaintext = (&plaintext_divided_by_r * &r.modulo(&self.public_key.N)).canonical_lift();

        Ok(plaintext)
    }

    /// [RSASP1][rsasp]
    ///
    /// [rsasp]: https://tools.ietf.org/html/rfc8017#section-5.2.1
    pub fn signature_primitive(&self, msg: &[u8]) -> Result<Long<D>> {
        self.decryption_primitive(msg)
    }

    /// Sign a message with respect to a padding method.
    pub fn sign<P, R>(&self, msg: &[u8], _padding: P, rng: R) -> Result<Long<D>>
    where
        P: SignaturePadding<D>,
        R: CryptoRng + RngCore,
    {
        let padded = P::pad(msg, rng).map_err(|_| Error)?;
        self.signature_primitive(&padded.to_bytes())
    }

    /// Decrypt a ciphertext with respect to a padding method.
    pub fn decrypt<P>(&self, ciphertext: &[u8], _: P) -> Result<Unpadded<D>>
    where
        P: EncryptionPadding<D>,
    {
        let padded_plaintext = self.decryption_primitive(ciphertext)?;
        P::unpad(&padded_plaintext).map_err(|_| Error)
    }

}

impl<const D: usize> From<(&ShortPrime<D>, &ShortPrime<D>)> for PublicKey<D> {
    fn from(prime_pair: (&ShortPrime<D>, &ShortPrime<D>)) -> Self {
        let (p, q) = prime_pair;
        PublicKey {
            N: Convenient(Odd((p.as_unsigned() * q.as_unsigned()).to_unsigned().unwrap()))
        }

    }
}

#[derive(Zeroize)]
pub struct Precomputed<const L: usize> {
    pub(crate) dp: Odd<L, 0>,
    pub(crate) dq: Odd<L, 0>,
    #[cfg(feature = "q-inverse")]
    pub(crate) q_inv: Short<L>,
}

impl<const D: usize> From<(&ShortPrime<D>, &ShortPrime<D>)> for Precomputed<D> {
    fn from(prime_pair: (&ShortPrime<D>, &ShortPrime<D>)) -> Self {
        // the trick here is to use Arazi Inversion as in JP03.
        //
        // We have $e = F4 = 65537$, and want
        // $d_p = e^{-1} mod p$ and $d_q$, the private exponents.
        let (p, q) = prime_pair;
        let dp = crate::F4::inv_mod(&p.wrapping_sub(&Short::from(1)));
        let dq = crate::F4::inv_mod(&q.wrapping_sub(&Short::from(1)));

        #[cfg(feature = "q-inverse")]
        let q_inv = q.modulo_prime(p).inverse().canonical_lift();

        #[cfg(not(feature = "q-inverse"))]
        return Self { dp, dq };

        #[cfg(feature = "q-inverse")]
        Self { dp, dq, q_inv }
    }
}

/// RSA private key.
///
/// Fundamentally, this consists of two different primes `p` and `q`, which should
/// both have bit length 8*L (i.e., L*4 bytes).
/// Additionally, `d_p = e^{-1} (mod p)` and `d_q = e^{-1} (mod q)` are stored.
///
/// It's quite sad, but we can't enforce the bound `L2 = 2*L`.
#[derive(Zeroize)]
pub struct PrivateKey<const D: usize> {
    pub(crate) p: ShortPrime<D>,
    // dp: ModInt<L>,
    pub(crate) q: ShortPrime<D>,
    // dq: ModInt<L>,
    pub(crate) precomputed: Precomputed<D>,
    pub(crate) public_key: PublicKey<D>,

}

impl<const D: usize> Bits for PrivateKey<D> {
    const BITS: usize = <Long<D> as Bits>::BITS;
}

impl<const D: usize> From<(ShortPrime<D>, ShortPrime<D>)> for PrivateKey<D> {
    fn from(prime_pair: (ShortPrime<D>, ShortPrime<D>)) -> Self {
        let (p, q) = prime_pair;
        #[allow(non_snake_case)]
        let N: Long<D> = (p.as_ref().as_ref() * q.as_ref().as_ref()).into_long();
        let public_key = PublicKey { N: Convenient(Odd(N)) };
        let precomputed: Precomputed<D> = (&p, &q).into();

        let private_key = PrivateKey { p, q, precomputed, public_key };
        private_key
    }
}

#[allow(dead_code)]
fn generate_prime_pair<const D: usize>() -> (ShortPrime<D>, ShortPrime<D>) {
    todo!();
}

impl<const L: usize> PrivateKey<L> {
     pub fn new(_rng: impl RngCore + CryptoRng) -> Result<Self> {
         // let (p, q) = generate_prime_pair();
         todo!();
         // let precomputed = precompute(&p, &q);
         // let public = PublicKey { N: p.as_ref().as_ref() * q.as_ref().as_ref() };
         // Ok(Self { p, q, precomputed, public })
     }
}

// 256 bits, in digits, for the primes of a private key
const RSA_5C_DIGITS: usize = 512 / <Digit as Bits>::BITS / 2;

// 512 bits, in digits, for the primes of a private key
const RSA_1K_DIGITS: usize = 1024 / <Digit as Bits>::BITS / 2;

// // 1024 bits, in digits, for the primes of a private key
// const RSA_2K_DIGITS: usize = 2048 / <Digit as Bits>::BITS / 2;

// // 1536 bits, in digits, for the primes of a private key
// const RSA_3K_DIGITS: usize = 3072 / <Digit as Bits>::BITS / 2;

// // 2048 bits, in digits, for the primes of a private key
// const RSA_4K_DIGITS: usize = 4096 / <Digit as Bits>::BITS / 2;

/// The RSA cryptosystem. Sealed trait to avoid experiments.
pub trait Rsa: sealed::Rsa {
    const DIGITS: usize;

    type PrivateKey;
    type PublicKey;
}

/// cf. https://rust-lang.github.io/api-guidelines/future-proofing.html#sealed-traits-protect-against-downstream-implementations-c-sealed
mod sealed {
    pub trait Rsa {}
    impl Rsa for super::Rsa5c {}
    impl Rsa for super::Rsa1k {}
    // impl Rsa for super::Rsa2k {}
    // impl Rsa for super::Rsa3k {}
    // impl Rsa for super::Rsa4k {}
}

// struct RsaType<const L: usize>;

// impl<const L: usize> RsaType<L> {
//     type PrivateKey = PrivateKey<L>;
//     type PublicKey = PrivateKey<L>;
// }

/// The RSA cryptosystem with 512 bit size keys.
pub struct Rsa5c;
impl Rsa for Rsa5c {
    const DIGITS: usize = RSA_5C_DIGITS;
    type PrivateKey = PrivateKey<RSA_5C_DIGITS>;
    type PublicKey = PublicKey<RSA_5C_DIGITS>;
}


/// The RSA cryptosystem with 1024 bit size keys.
pub struct Rsa1k;
impl Rsa for Rsa1k {
    const DIGITS: usize = RSA_1K_DIGITS;
    type PrivateKey = PrivateKey<RSA_1K_DIGITS>;
    type PublicKey = PublicKey<RSA_1K_DIGITS>;
}

///// The RSA cryptosystem with 2048 bit size keys.
/////
///// Corresponds roughly to 112-bit security.
//pub struct Rsa2k;
//impl Rsa<RSA_2K_DIGITS> for Rsa2k {}

///// The RSA cryptosystem with 3072 bit size keys.
/////
///// Corresponds roughly to 128-bit security.
//pub struct Rsa3k;
//impl Rsa<RSA_3K_DIGITS> for Rsa3k {}

///// The RSA cryptosystem with 4096 bit size keys.
//pub struct Rsa4k;
//impl Rsa<RSA_4K_DIGITS> for Rsa4k {}

// pub trait RSA {
//     const L: usize;
//     const L_plus_one: usize;
//     const L_times_two: usize;
// }

// pub struct RsaPublicKey<R: RSA> {
//     pub N: crate::Unsigned<{R::L}>,
// }

#[cfg(test)]
mod test {
    use crate::fixtures::*;

    #[test]
    fn primitives() {
        let msg_ = msg480().to_bytes();
        let msg = msg_.as_bytes();
        let private: <Rsa5c as Rsa>::PrivateKey = (pp256(), qq256()).into();
        let public = &private.public_key;

        // encrypt then decrypt
        let ciphertext = public.encryption_primitive(msg).unwrap().to_bytes();
        assert_eq!(
            &*ciphertext,
            &hex!("0a5cd90c81e1626b19fa9ccd34d3dcdef1481c72189cbc3c6bced3e426ef8352db3d65691125080a4eb8491804a74789434e3b6292f6d17aa892e229bea4d7e5"),
        );

        let decrypted = private.decryption_primitive(&ciphertext).unwrap().to_bytes();
        assert_eq!(msg, &*decrypted);

        // decrypt then encrypt
        let signature = private.signature_primitive(msg).unwrap().to_bytes();
        assert_eq!(
            &*signature,
            &hex!("af735869c96b330835198115a60598f7b9ce6e9354eda7e20746645ec8c5783b8c4f03c3dd1a538600c8d56f0a7a561137337646cc1183471b5090c39623ec92"),
        );

        let encrypted = public.encryption_primitive(&signature).unwrap().to_bytes();

        assert_eq!(msg, &*encrypted);

    }

    #[test]
    fn inversion_free() {
        let msg = msg480().to_bytes();
        let ciphertext = msg.as_bytes();
        let private: <Rsa5c as Rsa>::PrivateKey = (pp256(), qq256()).into();

        let plaintext = private.inversion_free_decryption(&ciphertext).unwrap().to_bytes();
        assert_eq!(
            &*plaintext,
            &hex!("af735869c96b330835198115a60598f7b9ce6e9354eda7e20746645ec8c5783b8c4f03c3dd1a538600c8d56f0a7a561137337646cc1183471b5090c39623ec92"),
        );

        let rng = crate::fixtures::CountingRng(0);
        let plaintext_using_blinding = private.blinded_inversion_free_decryption(rng, &ciphertext).unwrap().to_bytes();
        assert_eq!(
            &*plaintext_using_blinding,
            &hex!("af735869c96b330835198115a60598f7b9ce6e9354eda7e20746645ec8c5783b8c4f03c3dd1a538600c8d56f0a7a561137337646cc1183471b5090c39623ec92"),
        );
    }

    #[test]
    #[cfg(feature = "sha2-sig")]
    fn sign_pkcs1_sha256() {
        use crate::padding::*;

        let msg = b"yamnord";
        let private_key: <Rsa5c as Rsa>::PrivateKey = (pp256(), qq256()).into();
        let padding = Pkcs1::<sha2::Sha256>::default();
        let rng = crate::fixtures::CountingRng(0);

        let signature = private_key.sign(msg, padding, rng).unwrap().to_bytes();

        assert_eq!(signature.as_bytes(), &hex!(
            "106799571a87cdb31386fbd2d0ea7642bb196eba7979e64197fe51e1f4b1c32547988d33647144f518bb6c6ae986589f30102e5c6c9e720d0ccb376e2374fc14"
        ));
    }

    #[test]
    #[cfg(feature = "sha2-sig")]
    fn verify_pkcs1_sha256() {
        use crate::padding::*;

        let msg = b"yamnord";
        let private_key: <Rsa5c as Rsa>::PrivateKey = (pp256(), qq256()).into();
        let public_key = private_key.public_key;
        let padding = Pkcs1::<sha2::Sha256>::default();

        let signature = &hex!(
            "106799571a87cdb31386fbd2d0ea7642bb196eba7979e64197fe51e1f4b1c32547988d33647144f518bb6c6ae986589f30102e5c6c9e720d0ccb376e2374fc14");

        assert!(public_key.verify(msg, signature, padding).is_ok());
    }

    #[test]
    #[cfg(feature = "sha2-sig")]
    fn encrypt_pkcs1_sha256() {
        use crate::padding::*;

        let plaintext = b"yamnord";
        let private_key: <Rsa5c as Rsa>::PrivateKey = (pp256(), qq256()).into();
        let public_key = private_key.public_key;
        let padding = Pkcs1::<sha2::Sha256>::default();
        let rng = crate::fixtures::CountingRng(0);

        let encrypted = public_key.encrypt(plaintext, padding, rng).unwrap().to_bytes();

        // verified decryptable with pypa/cryptography
        // panic!("{}", delog::hex_str!(encrypted.as_bytes(), 64));
        assert_eq!(encrypted.as_bytes(), &hex!(
            "CF5A24F277F41575C22E785E669B1813B6DCD2F0BEAF87AB640A134247202D99D63EC56D6AD21864E558A0C923AFD6361297F8D18B3DB4FF8CB2CD4AE09FB755"
        ));
    }

    #[test]
    #[cfg(feature = "sha2-sig")]
    fn decrypt_pkcs1_sha256() {
        use crate::padding::*;

        let ciphertext = &hex!("aacdd6f270b8e1135e57813986ba5524bcc1a5a628b8fc34784977605956b5f328ae4df33cc005c5e9523dd41cafcdfc8ab6fc2106f63809de589fae2d382b52");
        let private_key: <Rsa5c as Rsa>::PrivateKey = (pp256(), qq256()).into();
        let padding = Pkcs1::<sha2::Sha256>::default();

        let decrypted = private_key.decrypt(ciphertext, padding).unwrap();

        assert_eq!(decrypted.as_bytes(), b"yamnord");
    }

    #[test]
    #[cfg(feature = "sha2-sig")]
    fn encrypt_oaep_sha256() {
        use crate::padding::*;

        let plaintext = b"yamnord";
        let private_key: <Rsa1k as Rsa>::PrivateKey = (p512(), q512()).into();
        let public_key = private_key.public_key;
        let padding = Oaep::<sha2::Sha256>::default();
        let rng = crate::fixtures::CountingRng(0);

        let encrypted = public_key.encrypt(plaintext, padding, rng).unwrap().to_bytes();

        // verified decryptable with pypa/cryptography
        // panic!("{}", delog::hex_str!(encrypted.as_bytes(), 64, sep: "\n"));
        assert_eq!(encrypted.as_bytes(), &hex!(
            "09875B38DF82E6DB9FB7503C4DF5D1CA59D980E2B22AA29E4E4BE9E34C8266A72844F57BE1B9EF141A5199ED34A60B1B8868C368F6AFDE65C8F33761043C084524BBB8187D93114CAD1297F9DE72B1299894B73EF0F1CD2E84E9C49AA12616BD2E881DA218FBF75539665A51C3524A20F155D16094B0584BAAE8D4B363739DCA"));
    }

    #[test]
    #[cfg(feature = "sha2-sig")]
    fn decrypt_oaep_sha256() {
        use crate::padding::*;

        let ciphertext = &hex!("94821467f7b7fd569379bdf682582a3c6ab8a3b47e12d026af3edfccbf7983a5327b82f7ae3fb9ba750b0e71e0108f4ad91d5ace86502d68737fe3da297a8ef96d8735a261afe61844d8668410ea917284065073dbf4542318f8becfbe5b44dafb6592176049323f4a3d3f9267855d3e5729fd8adf7ef41594fb9e2af7db2254");
        let private_key: <Rsa1k as Rsa>::PrivateKey = (p512(), q512()).into();
        let padding = Oaep::<sha2::Sha256>::default();

        let decrypted = private_key.decrypt(ciphertext, padding).unwrap();

        assert_eq!(decrypted.as_bytes(), b"yamnord");
    }

}
