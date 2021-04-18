#![cfg_attr(not(test), no_std)]
//! Allocation-free implementation of [R][rsa-patent][SA][rsa-rfc] for the standard cases.
//!
//! The implementation is fairly efficient as:
//! - we avoid GCD algorithms following [GCD-Free Algorithms for Computing Modular Inverses (Joye/Paillier, 2003)][jp03]
//! - our prime generation is fast following [Improvements to RSA key generation and CRT on embedded devices (Hamburg/Tunstall/Xiao, 2020)][htx20]
//!
//! [rsa-patent]: http://patft.uspto.gov/netacgi/nph-Parser?Sect1=PTO1&Sect2=HITOFF&p=1&u=/netahtml/PTO/srchnum.html&r=1&f=G&l=50&d=PALL&s1=4405829.PN.
//! [rsa-rfc]: https://tools.ietf.org/html/rfc8017
//! [jp03]: https://api.semanticscholar.org/CorpusID:17736455
//! [htx20]: https://api.semanticscholar.org/CorpusID:230108960

// Can't implement for this :/
// pub use core::num::Wrapping;

pub mod aliases;

pub mod arithmetic;
pub use arithmetic::Modular;
pub(crate) use arithmetic::{Montgomery, Wrapping};

mod digit;
pub use digit::{Digit, Digits};
pub(crate) use digit::{DoubleDigit, SignedDoubleDigit};

mod error;
pub use error::{Error, Result};

#[cfg(test)]
// pub(crate) mod fixtures;
pub mod fixtures;

mod f4;
pub use f4::F4;

mod key;
pub use key::{PrivateKey, PublicKey};
pub use key::{Rsa, /*Rsa2k, Rsa3k, Rsa4k*/};
#[cfg(feature = "yolo")]
pub use key::{Rsa5c, /*Rsa1k*/};

pub mod numbers;
pub use numbers::{Convenient, Long, Odd, Prime, Short, ShortPrime, Unsigned};
// pub(crate) use numbers::{Array, Number ,NumberMut};

pub(crate) mod padding;
pub use padding::{Oaep, Pss, Pkcs1V1_5};
mod primitive;


/// Intention is to replace this with the UMAAL assembly instruction on Cortex-M4.
///
/// Operation: `(hi, lo) = m*n + hi + lo`
///
/// This works, because `(2^32 - 1)^2 + 2*(2^32 - 1) = 2^64 - 1`.
#[allow(dead_code)]
#[allow(unstable_name_collisions)]
pub fn umaal(hi: &mut Digit, lo: &mut Digit, m: Digit, n: Digit) {
    use crate::numbers::Bits;
    let result = ((m as DoubleDigit) * (n as DoubleDigit)) + (*hi as DoubleDigit) + (*lo as DoubleDigit);
    *hi = (result >> Digit::BITS) as Digit;
    *lo = result as Digit;
}

