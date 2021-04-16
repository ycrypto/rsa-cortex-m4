/// A word on the machine. [`Unsigned`] is composed of many digits.
///
/// Feature `u32` forces the digit to be 32-bit even on 64-bit architectures,
/// feature `u64` forces the digit to be 64-bit even on 32-bit architectures.
///
/// This is done only for easier testing (typically embedded targets are 32 bit,
/// while desktop/server targets as 64 bit).
pub type Digit = digit::Digit;

/// Multiple [`Digit`]s. Since this type is unsized, we use [`Number`].
pub type Digits = [Digit];

/// Unsigned type with twice as many bits as [`Digit`].
pub(crate) type DoubleDigit = digit::DoubleDigit;
/// Signed type with twice as many bits as [`Digit`].
pub(crate) type SignedDoubleDigit = digit::SignedDoubleDigit;

#[cfg(not(any(feature = "u32", feature = "u64")))]
compile_error!("Either feature u32 or feature u64!");

#[cfg(all(feature = "u32", feature = "u64"))]
compile_error!("Either feature u32 or feature u64, not both!");

#[cfg(feature = "u32")]
mod digit {
    pub type Digit = u32;
    pub type DoubleDigit = u64;
    pub type SignedDoubleDigit = i64;
}

#[cfg(feature = "u64")]
mod digit {
    pub type Digit = u64;
    pub type DoubleDigit = u128;
    pub type SignedDoubleDigit = i128;
}

