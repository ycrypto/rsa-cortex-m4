#![cfg_attr(not(test), no_std)]
//! Allocation-free implementation of [R][rsa-patent][SA][rsa-rfc] for the standard cases.
//!
//! The implementation is fairly efficient as:
//! - we avoid GCD algorithms following [GCD-Free Algorithms for Computing Modular Inverses (Joye/Paillier, 2003)][jp03]
//! - our prime generation is fast following [Improvements to RSA key generation and CRT on embedded devices (Hamburg/Tunstall/Xiao, 2020)][htx20]
//!
//!
//!## PKCS #1 (RSA) revision history
//! - v1.1-1.3, February-March 1991
//! - v1.4, June 1991
//! - [RFC 2313, March 1998][rfc-2313] (v1.5, November 1993): the origin (+adds MD4)
//! - [RFC 2437, October 1998][rfc-2437] (v2.0, September 1998): introduces OAEP (+removes MD4)
//! - [RFC 3447, February 2003][rfc-3447] (v2.1, June 2002): introduces PSS (+multi-prime RSA)
//! - [RFC 8017, November 2016][rsa-rfc] (v2.2, October 2012): adds SHA2: 224, 512/224, 512/256 ("for FIPS 180-4 alignment")
//!
//! Bleichenbacher's attack (chosen ciphertexts) on RSAES in 1998 caused v2.0,
//! updated in [2006 with forgery attacks against RSASSA][bleichenbacher06].
//!
//! [Actual RSA v2.2 (2012)][rsa-v2_2]
//!
//! [rsa-patent]: http://patft.uspto.gov/netacgi/nph-Parser?Sect1=PTO1&Sect2=HITOFF&p=1&u=/netahtml/PTO/srchnum.html&r=1&f=G&l=50&d=PALL&s1=4405829.PN.
//! [rfc-2313]: https://tools.ietf.org/html/rfc2313
//! [rfc-2437]: https://tools.ietf.org/html/rfc2437
//! [rfc-3447]: https://tools.ietf.org/html/rfc3447
//! [rsa-rfc]: https://tools.ietf.org/html/rfc8017
//! [rsa-v2_2]: http://mpqs.free.fr/h11300-pkcs-1v2-2-rsa-cryptography-standard-wp_EMC_Corporation_Public-Key_Cryptography_Standards_(PKCS).pdf
//! [bleichenbacher06]: https://mailarchive.ietf.org/arch/msg/openpgp/5rnE9ZRN1AokBVj3VqblGlP63QE/
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

pub mod padding;
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

