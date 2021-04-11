/// A word on the machine. [`Unsigned`] is composed of many digits.
///
/// Feature `u32` forces the digit to be 32-bit even on 64-bit architectures,
/// this is done only for easier testing (typically embedded targets are 32 bit,
/// while desktop/server targets as 64 bit).
pub type Digit = digit::Digit;

/// Multiple [`Digit`]s. Since this type is unsized, we use [`Number`].
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

