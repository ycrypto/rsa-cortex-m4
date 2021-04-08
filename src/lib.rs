#![cfg_attr(not(test), no_std)]
//! Allocation-free implementation of [RSA][rsa] for the standard cases.
//!
//! [rsa]: http://patft.uspto.gov/netacgi/nph-Parser?Sect1=PTO1&Sect2=HITOFF&p=1&u=/netahtml/PTO/srchnum.html&r=1&f=G&l=50&d=PALL&s1=4405829.PN.
pub mod arithmetic;
pub use arithmetic::{Modular, Montgomery};
mod error;
pub use error::{Error, Result};
// mod key;
// pub use key::{PrivateKey, PublicKey};
// pub use key::{Rsa, Rsa2k, Rsa3k, Rsa4k};
pub mod numbers;
pub use numbers::{
    // Number ,NumberMut,
    // Array,
    Convenient, Long, Odd, Prime, Short, Unsigned,
};

/// A word on the machine. [`Unsigned`] is composed of many digits.
#[cfg(feature = "always-u32-digits")]
pub type Digit = u32;
#[cfg(not(feature = "always-u32-digits"))]
pub type Digit = usize;

// The DIGIT_SIZE_CHECK is a compile-time assertion
// that Digit is of expected bit size.

// #[cfg(target_pointer_width = "16")]
// #[allow(dead_code)]
// const DIGIT_SIZE_CHECK: usize = (core::mem::size_of::<Digit>() == core::mem::size_of::<u16>()) as usize - 1;
// #[cfg(target_pointer_width = "16")]
// pub(crate) type DoubleDigit = u32;
// #[cfg(target_pointer_width = "16")]
// pub(crate) type SignedDoubleDigit = i32;

#[cfg(any(target_pointer_width = "32", feature = "always-u32-digits"))]
#[allow(dead_code)]
const DIGIT_SIZE_CHECK: usize = (core::mem::size_of::<Digit>() == core::mem::size_of::<u32>()) as usize - 1;
#[cfg(any(target_pointer_width = "32", feature = "always-u32-digits"))]
pub(crate) type DoubleDigit = u64;
#[cfg(any(target_pointer_width = "32", feature = "always-u32-digits"))]
pub(crate) type SignedDoubleDigit = i64;

#[cfg(all(target_pointer_width = "64", not(feature = "always-u32-digits")))]
#[allow(dead_code)]
const DIGIT_SIZE_CHECK: usize = (core::mem::size_of::<Digit>() == core::mem::size_of::<u64>()) as usize - 1;
#[cfg(all(target_pointer_width = "64", not(feature = "always-u32-digits")))]
pub(crate) type DoubleDigit = u128;
#[cfg(all(target_pointer_width = "64", not(feature = "always-u32-digits")))]
pub(crate) type SignedDoubleDigit = i128;

// mod primitive;


/// The fourth Fermat prime, $2^{16} + 1$.
///
/// This library only implements RSA keys with public exponent `e = 65537 = 0x10001 = u16::MAX + 2`.
///
/// An example recommendation to do so is RFC 4871: <https://www.ietf.org/rfc/rfc4871.txt>,
/// more generally, there seems no need to have too many knobs to turn.
///
pub const F4: Digit = 0x1_0001;
