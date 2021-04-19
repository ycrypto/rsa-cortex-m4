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
    /// [rsavp]: https://tools.ietf.org/html/rfc8017#section-5.2.2
    pub fn verification_primitive(&self, signature: &[u8]) -> Result<Long<D>> {
        self.encryption_primitive(signature)
    }
}

impl<const D: usize> PrivateKey<D> {
    fn q_inv_mod_p(&self) -> PrimeModular<'_, D, 0> {
        PrimeModular { x: self.precomputed.q_inv.clone(), p: &self.p }
    }

    /// [RSADP][rsadp]
    ///
    /// [rsadp]: https://tools.ietf.org/html/rfc8017#section-5.1.2
    pub fn decryption_primitive(&self, ciphertext: &[u8]) -> Result<Long<D>> {

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

    /// [RSASP1][rsasp]
    ///
    /// [rsasp]: https://tools.ietf.org/html/rfc8017#section-5.2.1
    pub fn signature_primitive(&self, msg: &[u8]) -> Result<Long<D>> {
        self.decryption_primitive(msg)
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

// Since e = 65537 is prime, can use Arazi's inversion formula
// to calculate `e^{-1} (mod p - 1)`:
// https://link.springer.com/content/pdf/10.1007%2F978-3-540-45238-6_20.pdf
//
// Namely, `d = (1 + f(-f^{e -2} mod e) / e`.
//
// This integer division by e can further be simplified by calculating
// `e^{-1} (mod 2^|f|)`, where |f| is the bit length, and multiplying by that.
//
// This can be hard-coded, or calculated with modular operations as explained in Fig. 1 (loc. cit.)
//
//
//
// Example:
// ? e = 0x10001;
// ? p = nextprime(random(10^25))
// %30 = 7924439388568400274982499
// ? f = p - 1;
//
// Goal is to calculate:
// ? lift(1/Mod(e, p - 1))
// %33 = 666365342789576177051567
//
// Note that lift(Mod(f, e)) is a u32
// ? lift(-Mod(f, e)^(e - 2))
// %37 = 5511
//
// ? lift((1 + f*Mod(5511, 2^fbits))*(1/Mod(e, 2^fbits)))
// %41 = 666365342789576177051567

// fn precompute_e_inverse<const L: usize>(p: &ShortPrime<L>) -> Unsigned<L> {
//     let f = p - 1;
//     // Since e is prime, inverses modulo e are given by x.power(e - 2), by Fermat's little theorem.
//     // This is a small exponentiation to the 0xFFFF
//     let f_inverse_mod_e = f.modulo(crate::E).to_the(crate::E - 2);

//     let minus_f_inverse = (-(f.modulo(crate::E).pow(65536))).lift();
//     let denominator = 1 + f * (-f_inverse_mod_e).lift();

//     // This integer division
//     let e_inverse = denominator / e;
//     e_inverse
// }

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

// // 512 bits, in digits, for the primes of a private key
// const RSA_1K_DIGITS: usize = 1024 / <Digit as Bits>::BITS / 2;

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
    // impl Rsa for super::Rsa1k {}
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


///// The RSA cryptosystem with 1024 bit size keys.
//pub struct Rsa1k;
//impl Rsa<RSA_1K_DIGITS> for Rsa1k {}

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
}
