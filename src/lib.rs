#![cfg_attr(not(test), no_std)]
//! Allocation-free implementation of [RSA][rsa] for the standard cases.
//!
//! [rsa]: http://patft.uspto.gov/netacgi/nph-Parser?Sect1=PTO1&Sect2=HITOFF&p=1&u=/netahtml/PTO/srchnum.html&r=1&f=G&l=50&d=PALL&s1=4405829.PN.

// Can't implement for this :/
// pub use core::num::Wrapping;

pub mod arithmetic;
pub use arithmetic::Modular;
pub(crate) use arithmetic::{Montgomery, Wrapping};
mod error;
pub use error::{Error, Result};
// mod key;
// pub use key::{PrivateKey, PublicKey};
// pub use key::{Rsa, Rsa2k, Rsa3k, Rsa4k};

pub mod numbers;
pub use numbers::{Convenient, Long, Odd, Prime, Short, Unsigned};
// pub(crate) use numbers::{Array, Number ,NumberMut};

/// A word on the machine. [`Unsigned`] is composed of many digits.
///
/// Feature `u32` forces the digit to be 32-bit even on 64-bit architectures,
/// this is done only for easier testing (typically embedded targets are 32 bit,
/// while desktop/server targets as 64 bit).
pub type Digit = digit::Digit;

/// Multiple [`Digit`]s. Since this type is unsized, we use [`numbers::Number`].
pub type Digits = [Digit];

/// Unsigned type with twice as many bits as [`Digit`].
pub(crate) type DoubleDigit = digit::DoubleDigit;
/// Signed type with twice as many bits as [`Digit`].
pub(crate) type SignedDoubleDigit = digit::SignedDoubleDigit;

// The DIGIT_SIZE_CHECK is a compile-time assertion
// that Digit is of expected bit size.

// #[cfg(target_pointer_width = "16")]
// #[allow(dead_code)]
// const DIGIT_SIZE_CHECK: usize = (core::mem::size_of::<Digit>() == core::mem::size_of::<u16>()) as usize - 1;
// #[cfg(target_pointer_width = "16")]
// pub(crate) type DoubleDigit = u32;
// #[cfg(target_pointer_width = "16")]
// pub(crate) type SignedDoubleDigit = i32;

mod digit {
    #[cfg(feature = "u32")]
    pub type Digit = u32;
    #[cfg(not(feature = "u32"))]
    pub type Digit = usize;

    #[cfg(any(target_pointer_width = "32", feature = "u32"))]
    #[allow(dead_code)]
    const DIGIT_SIZE_CHECK: usize = (core::mem::size_of::<Digit>() == core::mem::size_of::<u32>()) as usize - 1;
    #[cfg(any(target_pointer_width = "32", feature = "u32"))]
    pub(crate) type DoubleDigit = u64;
    #[cfg(any(target_pointer_width = "32", feature = "u32"))]
    pub(crate) type SignedDoubleDigit = i64;

    #[cfg(all(target_pointer_width = "64", not(feature = "u32")))]
    #[allow(dead_code)]
    const DIGIT_SIZE_CHECK: usize = (core::mem::size_of::<Digit>() == core::mem::size_of::<u64>()) as usize - 1;
    #[cfg(all(target_pointer_width = "64", not(feature = "u32")))]
    pub(crate) type DoubleDigit = u128;
    #[cfg(all(target_pointer_width = "64", not(feature = "u32")))]
    pub(crate) type SignedDoubleDigit = i128;
}

// mod primitive;


/// The fourth Fermat prime, $2^{16} + 1$.
///
/// This library only implements RSA keys with public exponent `e = 65537 = 0x10001 = u16::MAX + 2`.
///
/// An example recommendation to do so is RFC 4871: <https://www.ietf.org/rfc/rfc4871.txt>,
/// more generally, there seems no need to have too many knobs to turn.
///
pub const F4: Digit = 0x1_0001;


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

