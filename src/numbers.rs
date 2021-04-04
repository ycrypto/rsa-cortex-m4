#![allow(unstable_name_collisions)]  // for Bits::BITS

use core::ops::{Deref, DerefMut};

use zeroize::Zeroize;

use crate::{Error, Result};

mod trait_implementations;

/// `u32`
pub type Digit = u32;
pub type DoubleDigit = u64;
pub type SignedDoubleDigit = i64;

/// The unstable `{number}::BITS` implementations.
pub trait Bits {
    const BITS: usize;
}

/// Something similar to a `Vec<u32>`, without allocations.
///
/// Implementation ***must ensure***:
/// - `self.len() == self.words().len()`
/// - `self.capacity() == self.words_mut().len()`
/// - `Deref` coincides with `self.words()`
/// - `DerefMut` coincides with `self.words_mut()`
///
/// There is no need to "extend" the allocation, simply write to
/// the desired index / slice (via DerefMut).
///
/// This may need to be revisited for efficiency reasons (calculating `len` over and over).
///
/// The highest non-zero term determines the leading digit and the length.
///
/// Current implementations are:
/// - `Unsigned<L>`
/// - `Product<M,N>`
pub unsafe trait AsNormalizedLittleEndianWords: Deref<Target = [u32]> + DerefMut {
    const CAPACITY: usize;

    fn len(&self) -> usize;

    fn capacity() -> usize {
        Self::CAPACITY
    }

    /// Default implementation assumes "data slice" starts at object address.
    fn words(&self) -> &[u32] {
        let l = self.len();
        unsafe { core::slice::from_raw_parts_mut(self as *const _ as _, l) }
    }

    /// Default implementation assumes "data slice" starts at object address.
    fn words_mut(&mut self) -> &mut [u32] {
        let l = Self::capacity();
        unsafe { core::slice::from_raw_parts_mut(self as *mut _ as _, l) }
    }

    fn leading_digit(&self) -> Option<Digit> {
        self.last().map(|&d| d)
    }

    /// Embed in array of capacity C, if possible.
    ///
    /// Fails: iff `self.len() > C`.
    ///
    /// Not expressable as `TryInto`, as it would clash with blanket implementations,
    /// e.g. for Unsigned<L> with C = L.
    fn try_into_unsigned<const C: usize>(&self) -> Result<Unsigned<C>> {
        let l = self.len();
        if l <= C {
            Ok(Unsigned::<C>::from_slice(&self))
        } else {
            Err(Error)
        }
    }

    /// Panics if `try_into_unsigned` fails.
    fn into_unsigned<const C: usize>(&self) -> Unsigned<C> {
        self.try_into_unsigned().unwrap()
    }

}

// The following does not work.
//
// The problem is a) that WordsMut(&mut [u32]) is not a "place expression",
// so can't do on-the-fly wrapping like `Words(&mut q[j..]) += &other`.
//
// b) Index/IndexMut with ranges don't seem to work outside builtin [T] and str
// types, as IndexMut shares the "Output" type with Index, whereas
// Words(&slice) and WordsMut(&mut slice) are different.
//
//pub struct Words<'a>(pub &'a [Digit]);

///// Not sure if this type should be made prominent.
/////
///// Current use case is implementing AddAssign on a sub-range of an Unsigned,
///// while DerefMut's Output of [u32] (and hence ranges thereof) is foreign.
//pub struct WordsMut<'a>(pub &'a mut [Digit]);

//impl<'a> From<&'a mut [Digit]> for WordsMut<'a> {
//    fn from(digits: &'a mut [Digit]) -> Self {
//        Self(digits)
//    }
//}

/// Unsigned integer with `L` digits (L for length).
///
/// Internal representation as little-endian.
///
/// TODO: unify terminology (digits vs limbs)
///
/// In our "heapless" situation, we have no multiplication nor addition.
#[derive(Clone, Eq, Zeroize)]
// pub struct Unsigned<const L: usize>(Vec<Digit, L>);
pub struct Unsigned<const L: usize>(pub(crate) [Digit; L]);

unsafe impl<const L: usize> AsNormalizedLittleEndianWords for Unsigned<L> {
    const CAPACITY: usize = L;

    /// 0 if zero, else index + 1 of last non-zero digit
    fn len(&self) -> usize {
        self.0.iter()
            .enumerate().rev()
            .find(|(_, &x)| x != 0)
            .map(|(i, _)| i + 1)
            .unwrap_or(0)
    }
}

/// Fails for L = 0, bound not expressable.
impl<const L: usize> From<Digit> for Unsigned<L> {
    fn from(unsigned: Digit) -> Self {
        let mut r = Self::default();
        r.0[0] = unsigned;
        r
    }
}

/// Representation of Unsigned<L> as big-endian bytes.
pub struct BigEndian<const L: usize>([Digit; L]);

impl<const L: usize> BigEndian<L> {
    /// TODO: consider truncating leading zero bytes (needs some pointer arithmetique)
    pub fn as_be_bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(&self.0[0] as *const u32 as _, 4*L) }
    }
}

// c'tors and such
impl<const L: usize> Unsigned<L> {
    pub fn from_slice(slice: &[u32]) -> Self {
        let mut x = Self::zero();
        x.0[..slice.len()].copy_from_slice(slice);
        x
    }

    /// TODO: consider `into_be_bytes`, reusing the buffer.
    ///
    /// i.e.
    /// - swap words + endianness on self.0
    /// - return BigEndian(self.0)
    fn to_be_bytes(&self) -> BigEndian<L> {
        let mut big_endian = BigEndian([0; L]);
        // we need to store word such that it bytes are big-endian, whatever
        // the native architecture (although PC/Cortex are both little-endian).
        for i in 0..L {
            // "On big endian this is a no-op. On little endian the bytes are swapped."
            big_endian.0[L - i - 1] = u32::from_be(self.0[i]);
        }
        big_endian
    }
}

/// Trait methods as inherent methods, for convenience.
impl<const L: usize> Unsigned<L> {
    pub fn leading_digit(&self) -> Option<Digit> {
        AsNormalizedLittleEndianWords::leading_digit(self)
    }
    pub fn try_into_unsigned<const C: usize>(&self) -> Result<Unsigned<C>> {
        AsNormalizedLittleEndianWords::try_into_unsigned(self)
    }
    pub fn into_unsigned<const C: usize>(&self) -> Unsigned<C> {
        AsNormalizedLittleEndianWords::into_unsigned(self)
    }
    pub fn one() -> Self {
        One::one()
    }
    pub fn zero() -> Self {
        Zero::zero()
    }
}


/// Product of two unsigned integers.
///
/// `Product<M, L>` is what `Unsigned<M + L>` would be, if const-generics on stable
/// would allow expressing this. This is a workaround type.
///
/// The special case `Product<L, 1>` has an alias `UnsignedCarry<L>`.
#[repr(C)]
#[derive(Clone, Default, Eq, PartialEq, Zeroize)]
pub struct Product<const M: usize, const N: usize> {
    // lo: [u32; M],
    // hi: [u32; N],
    lo: Unsigned<M>,
    hi: Unsigned<N>,
}

unsafe impl<const M: usize, const N: usize> AsNormalizedLittleEndianWords for Product<M, N> {
    const CAPACITY: usize = M + N;

    fn len(&self) -> usize {
        let l_hi = self.hi.len();
        if l_hi > 0 {
            M + l_hi
        } else {
            self.lo.len()
        }
    }
}

/// Trait methods as inherent methods, for convenience.
impl<const M: usize, const N: usize> Product<M, N> {
    pub fn leading_digit(&self) -> Option<Digit> {
        AsNormalizedLittleEndianWords::leading_digit(self)
    }
    pub fn try_into_unsigned<const C: usize>(&self) -> Result<Unsigned<C>> {
        AsNormalizedLittleEndianWords::try_into_unsigned(self)
    }
    pub fn into_unsigned<const C: usize>(&self) -> Unsigned<C> {
        AsNormalizedLittleEndianWords::into_unsigned(self)
    }
    pub fn one() -> Self {
        One::one()
    }
    pub fn zero() -> Self {
        Zero::zero()
    }
}

/// `Unsigned<L + 1>` aka `Product<L, 1>`.
///
/// Due to limitations in const-generics on stable, we can't express
/// `Unsigned<L + 1>`. This is a workaround type.
pub type UnsignedCarry<const L: usize> = Product<L, 1>;

// c'tors and such
impl<const L: usize> UnsignedCarry<L> {
    pub fn from_array_and_carry(array: [u32; L], carry: u32) -> Self {
        Self {
            lo: Unsigned(array),
            hi: Unsigned([carry]),
        }
    }
    pub fn from_slice_and_carry(slice: &[u32], carry: u32) -> Self {
        Self {
            lo: Unsigned::from_slice(slice),
            hi: Unsigned::from_slice(&[carry]),
        }
    }
}

/// `Product<L, L>`
pub type Square<const L: usize> = Product<L, L>;

/// Unsigned integer that is non-zero and odd.
///
/// These are used as moduli.
///
/// The oddness condition ensures we can use Montgomery multiplication/reduction.
#[derive(Clone, Eq, PartialEq, Zeroize)]
// Q: rename to `PositivelyOdd`? :)
pub struct NonZeroOdd<const L: usize>(Unsigned<L>);

/// Odd prime.
#[derive(Clone, Eq, PartialEq, Zeroize)]
#[zeroize(drop)]
pub struct Prime<const L: usize>(NonZeroOdd<L>);

pub trait One: Sized + PartialEq {
    fn one() -> Self;

    fn is_one(&self) -> bool { *self == Self::one() }
    fn set_one(&mut self) { *self = Self::one(); }
}

pub trait Zero: Sized + PartialEq {
    fn zero() -> Self;

    fn is_zero(&self) -> bool { *self == Self::zero() }
    fn set_zero(&mut self) { *self = Self::zero(); }
}

// impl<const L: usize> One for Unsigned<L> {
impl<T: AsNormalizedLittleEndianWords + Default + PartialEq> One for T {
    fn one() -> Self {
        let mut one = Self::default();
        one[0] = 1;
        one
    }
}

impl<T: AsNormalizedLittleEndianWords + Default + PartialEq> Zero for T {
    fn zero() -> Self {
        Self::default()
    }

    fn is_zero(&self) -> bool {
        self.len() == 0
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn debug() {
        let u = Unsigned([0x76543210, 0xFEDCBA98]);
        assert_eq!(format!("{:X?}", u), "[FE, DC, BA, 98, 76, 54, 32, 10]");
    }

    #[test]
    fn len() {
        let x = Unsigned([0,1,0,2,0,0]);
        assert_eq!(x.len(), 4);

        let x = Unsigned([0, 0, 0]);
        assert_eq!(x.len(), 0);
    }

    #[test]
    fn partial_eq() {
        let p = Prime(NonZeroOdd(Unsigned([17, 0])));
        let u = Unsigned([17, 0]);
        assert_eq!(&p.0.0, &u);
    }

    #[test]
    fn product() {
        let prod = Square { lo: Unsigned([1,2,3]), hi: Unsigned([4,5,6]) };
        assert_eq!(prod.words().len(), 6);
        assert_eq!(prod.words(), &[1,2,3,4,5,6]);
    }

    #[test]
    fn unsigned_carry() {
        let uc = UnsignedCarry::from_array_and_carry([1,2,3], 4);
        assert_eq!(uc.words(), &[1,2,3,4]);
    }
}
