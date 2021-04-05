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

use crate::{Odd, Prime, Result, Unsigned};

/// RSA public key.
///
/// Here, `N = pq` is the product of the private pair of primes.
/// `e` is fixed to be 65537 = 0x10001.
#[allow(non_snake_case)]
#[derive(Zeroize)]
pub struct PublicKey<const L: usize> {
    pub N: Unsigned<L, L>,
}

#[derive(Zeroize)]
pub struct Precomputed<const L: usize> {
    dp: Odd<L, 0>,
    dq: Odd<L, 0>,
}

/// RSA private key.
///
/// Fundamentally, this consists of two different primes `p` and `q`, which should
/// both have bit length 8*L (i.e., L*4 bytes).
/// Additionally, `d_p = e^{-1} (mod p)` and `d_q = e^{-1} (mod q)` are stored.
///
/// It's quite sad, but we can't enforce the bound `L2 = 2*L`.
#[derive(Zeroize)]
pub struct PrivateKey<const L: usize> {
    p: Prime<L>,
    // dp: ModInt<L>,
    q: Prime<L>,
    // dq: ModInt<L>,
    precomputed: Precomputed<L>,
    public: PublicKey<L>,
}

#[allow(dead_code)]
fn generate_prime_pair<const L: usize>() -> (Prime<L>, Prime<L>) {
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

// fn precompute_e_inverse<const L: usize>(p: &Prime<L>) -> Unsigned<L> {
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

// 32 digits for the primes of a private key
const RSA_2K_SIZE: usize = 2048 / 32 / 2;

// 48 digits for the primes of a private key
const RSA_3K_SIZE: usize = 3072 / 32 / 2;

// 64 digits for the primes of a private key
const RSA_4K_SIZE: usize = 4096 / 32 / 2;

pub trait Rsa<const L: usize>: sealed::Rsa {
    type PrivateKey;//: crate::primitive::DecryptionPrimitive<L>;
    type PublicKey;
}

/// cf. https://rust-lang.github.io/api-guidelines/future-proofing.html#sealed-traits-protect-against-downstream-implementations-c-sealed
mod sealed {
    pub trait Rsa {}
    impl Rsa for super::Rsa2k {}
    impl Rsa for super::Rsa3k {}
    impl Rsa for super::Rsa4k {}
}

// struct RsaType<const L: usize>;

// impl<const L: usize> RsaType<L> {
//     type PrivateKey = PrivateKey<L>;
//     type PublicKey = PrivateKey<L>;
// }

/// The RSA cryptosystem with 2048 bit size keys.
pub struct Rsa2k;
impl Rsa<RSA_2K_SIZE> for Rsa2k {
    type PrivateKey = PrivateKey<RSA_2K_SIZE>;
    type PublicKey = PublicKey<RSA_2K_SIZE>;
}

/// The RSA cryptosystem with 3072 bit size keys.
///
/// Corresponds roughly to 128-bit security.
pub struct Rsa3k;
impl Rsa<RSA_3K_SIZE> for Rsa3k {
    type PrivateKey = PrivateKey<RSA_3K_SIZE>;
    type PublicKey = PublicKey<RSA_3K_SIZE>;
}

/// The RSA cryptosystem with 4096 bit size keys.
pub struct Rsa4k;
impl Rsa<RSA_4K_SIZE> for Rsa4k {
    type PrivateKey = PrivateKey<RSA_4K_SIZE>;
    type PublicKey = PublicKey<RSA_4K_SIZE>;
}


// pub trait RSA {
//     const L: usize;
//     const L_plus_one: usize;
//     const L_times_two: usize;
// }

// pub struct RsaPublicKey<R: RSA> {
//     pub N: crate::Unsigned<{R::L}>,
// }





