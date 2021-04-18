//! Large unsized integers (specialized to our *allocation-free* purposes).
//!
//! The internal representation is in terms of little-endian machine words.
//!
//! This specification of types was chosen after a few iterations of the options
//! within the limitations of [`min_const_generics`][min-const-generics].
//!
//! One advantage it has is that [`Short`] and [`Long`] integers (hence also short/long
//! [`crate::Montgomery`], etc.) can share implementations.
//!
//! [min-const-generics]: https://blog.rust-lang.org/2021/03/25/Rust-1.51.0.html#const-generics-mvp
#![allow(unstable_name_collisions)]  // for Bits::BITS

use core::{cmp::Ordering, mem::{align_of, size_of}, ops::{Deref, DerefMut}};

use ref_cast::RefCast;
use zeroize::Zeroize;

use crate::{Digit, Error, Result};

mod trait_implementations;


/// The unstable `{number}::BITS` implementations.
///
/// Cf. <https://github.com/rust-lang/rust/pull/76492>.
pub trait Bits {
    const BITS: usize;
    // const BYTES: usize;
}

/// Several [`Digit`]s attach to a limb.
pub type Limb<const D: usize> = [Digit; D];

/// Multi-precision unsigned integer with at most $D + E$ digits (places) – two [`Limb`]s.
///
/// Workaround type for limitations of const generics on stable;
/// the interesting cases are:
/// - [`Short`], where $E = 0$, and
/// - [`Long`], where $D = E$.
///
/// The former is used for RSA prime pairs $(P, Q)$, the latter for RSA public keys $N = PQ$.
///
/// Mnemonics: `D` for digits, `E` for "extra" digits.
//
// possible synonyms: Duplex, Twofold, (Dual)
// goal is not to evoke "twin", "double", which would imply both limbs are the same
#[repr(C)]
#[derive(Clone, Eq, Zeroize)]
pub struct Unsigned<const D: usize, const E: usize> {  // this is a kind of "dual number"
    lo: Limb<D>,
    hi: Limb<E>,
}

#[cfg(feature = "ct-maybe")]
impl<const D: usize, const E: usize> subtle::ConditionallySelectable for Unsigned<D, E> {
    fn conditional_select(a: &Self, b: &Self, c: subtle::Choice) -> Self {
        let mut selected = Unsigned::zero();
        for (s, (a, b)) in selected.iter_mut().zip(a.iter().zip(b.iter())) {
            *s = Digit::conditional_select(a, b, c);
        }
        selected

    }
}

// pub type Unsigned<const D: usize, const E: usize> = Array<D, E, 1>;

#[repr(transparent)]
#[derive(Clone, Debug, RefCast)]
pub struct Odd<const D: usize, const E: usize>(pub(crate) Unsigned<D, E>);

impl<const D: usize, const E: usize> Odd<D, E> {
    pub fn as_unsigned(&self) -> &Unsigned<D, E> {
        &self.0
    }
    pub fn into_unsigned(self) -> Unsigned<D, E> {
        self.0
    }
}

#[repr(transparent)]
#[derive(Clone, Debug, RefCast)]
/// Unsigned numbers with both their top and bottom bits set – highly convenient for modular
/// arithmetic!
///
/// In particular, they are odd. But also, $n \ge 2^{m - 1}$, with strict inequality
/// by oddness.
///
/// As described in [Incomplete reduction in modular arithmetic (2002)][yanik-savas-koc],
/// it is not necessary to reduce fully modulo `n` while calculating modular arithmetic.
/// Instead, we can reduce modulo $2^m$, and only "fully" reduce when so desired.
///
/// Their arguments apply to non-prime moduli also, and the "convenient" ones have the properties,
/// in their terminology, that $I = 1$ and $J = 2$, hence $F = 2^m - p$ and $G = 2p - 2^m$.
/// Moreover (!!!), the last case/reduction in their modular addition / subtraction never
/// occurs.
///
/// E.g., in addition, we have $F = 2^m - n < 2^m - 2^{m - 1} = 2^{m-1}$, and so
/// $T := S + F < (2^m - 2) + 2^{m - 1} < 2^{m - 1}$.
///
/// [yanik-savas-koc]: https://api.semanticscholar.org/CorpusID:17543811
pub struct Convenient<const D: usize, const E: usize>(pub(crate) Odd<D, E>);

impl<const D: usize, const E: usize> Convenient<D, E> {
    pub fn as_odd(&self) -> &Odd<D, E> {
        &self.0
    }
    pub fn into_odd(self) -> Odd<D, E> {
        self.0
    }
    pub fn as_unsigned(&self) -> &Unsigned<D, E> {
        &self.0.0
    }
    pub fn into_unsigned(self) -> Unsigned<D, E> {
        self.0.0
    }
}

#[repr(transparent)]
#[derive(Clone, Debug, RefCast)]
/// Prime number (passing primality tests); convenient by definition.
pub struct Prime<const D: usize, const E: usize>(pub(crate) Convenient<D, E>);

impl<const D: usize, const E: usize> Prime<D, E> {
    pub fn as_convenient(&self) -> &Convenient<D, E> {
        &self.0
    }
    pub fn into_convenient(self) -> Convenient<D, E> {
        self.0
    }
    pub fn as_odd(&self) -> &Odd<D, E> {
        &self.0.0
    }
    pub fn into_odd(self) -> Odd<D, E> {
        self.0.0
    }
    pub fn as_unsigned(&self) -> &Unsigned<D, E> {
        &self.0.0.0
    }
    pub fn into_unsigned(self) -> Unsigned<D, E> {
        self.0.0.0
    }
}

pub type ShortPrime<const D: usize> = Prime<D, 0>;

/// [`Unsigned`] with equal limbs (e.g., public key). If only we had `[T; 2*D]`...
pub type Long<const D: usize> = Unsigned<D, D>;  // duplex with equal limb size
/// [`Unsigned`] with only one limb (e.g., private prime). Short only in comparison to [`Long`].
pub type Short<const D: usize> = Unsigned<D, 0>;  // duplex with empty hi limb

// DO NOT DO THIS
//
// it's way too unsafe, can call self.padded_number() on result
//
//impl<const D: usize> Short<D> {
//    /// TODO.
//    ///
//    /// Idea: Can implement truncating arithmetic on Unsigned<D, E>,
//    /// and where needed, instead do:
//    ///
//    /// let (p, q): (Short<D>, Short<D>) = generate_primes();
//    /// let n: Product<D, D> = p.as_long() * q.as_long()  // <- using Mul for &Unsigned<D, D>
//    ///
//    /// to use "long" arithmetic on short unsigned numbers.
//    pub fn as_long(&self) -> &Long<D> {
//        unsafe { &*(self as *const _ as *const _) }
//    }
//}

#[repr(C)]
#[derive(Clone, Eq/*, Zeroize*/)]
/// Array of [`Unsigned`].
pub struct Array<const D: usize, const E: usize, const L: usize> {
    lo: [Limb<D>; L],
    hi: [Limb<E>; L],
}

// double duplex?
/// Big enough to fit the product of two [`Unsigned`].
pub type Product<const D: usize, const E: usize> = Array<D, E, 2>;

impl <const D: usize> Product<D, 0> {//Array<D, 0, 2> {
    pub fn into_long(self) -> Long<D> {
        Unsigned::<D, D> { lo: self.lo[0], hi: self.lo[1] }
    }

    pub fn as_long(&self) -> &Long<D> {
        unsafe { &*(self as *const _ as *const _) }
    }
}

/// Something similar to a `Vec<u32>`, without allocations.
///
/// The dereferenced slice is treated as little-endian digits of a big unsigned integer;
/// this slice must be of length `Self::DIGITS`.
///
/// There is no need to "extend" the allocation as in, say, `heapless`.
/// Simply write to the desired index / slice (via DerefMut).
///
/// In a previous version of this trait, only the significant digits (up until the leading digit)
/// were dereferenced. To meet constant-time requirements, this was changed.
///
/// Current implementations are (with const generic usize parameters):
/// - `Unsigned<D, E>`
/// - `Array<D, E, L>`
///
/// Of actual interest are Long (=`Unsigned<D, D>`) and Short (=`Unsigned<D, 0>`) numbers,
/// where "Short" is tongue-in-cheek.
///
/// A lot of this dance could be skipped if only sums of const generic usizes were
/// considered const (which they are not in Rust 1.51's `min_const_generics`.
///
/// All we really want is to have two "Short" primes $P, Q$, and their "Long" product $N = PQ$.
///
///
/// ## Implementing this trait
///
/// The type should consist of non-trivial consecutive Digit "plain old data", and be `Clone + Debug + Default`.
///
/// Then the following is all that is needed:
/// ```rust,ignore
/// impl Deref for T {
///   type Target = [Digit];
///   fn deref(&self) -> &Self::Target {
///     Number::deref(self)
///   }
/// }
/// impl DerefMut for T {
///   fn deref_mut(&mut self) -> &mut Self::Target {
///     Number::deref_mut(self)
///   }
/// }
/// unsafe impl Number for T {}
/// impl NumberMut for T {}
/// ```

// Not a huge fan of "sealing", but we could do it.
// mod sealed {
//     pub trait Number {}
//     impl<const D: usize, const E: usize, const L: usize> Number for crate::numbers::Array<D, E, L> {}
//     impl<const D: usize, const E: usize> Number for crate::Unsigned<D, E> {}
//     impl<T: Number> Number for crate::arithmetic::Wrapping<T> {}
// }

pub unsafe trait Number: /*sealed::Number +*/ Deref<Target = [Digit]> + Clone + core::fmt::Debug + Default { // + PartialEq + PartialOrd {

    /// The number of bits that fit in this number.
    const BITS: usize = core::mem::size_of::<Self>() * 8;

    #[deny(const_err)]
    /// The number of digits that fit in this number.
    ///
    /// There are compile-time checks that alignment and size of implementing types are compatible (i.e., multiples)
    /// with those of the digit type. If not, there are error messages of the form
    /// ``attempt to compute `0_usize - 1_usize`, which would overflow``.
    const DIGITS: usize = size_of::<Self>() / size_of::<Digit>()
        // check that size of self is multiple of size of digit
        + ((size_of::<Digit>() * (size_of::<Self>() / size_of::<Digit>()) == size_of::<Self>()) as usize - 1)
        // check that alignment of self is multiple of alignment of digit
        + ((align_of::<Digit>() * (align_of::<Self>() / align_of::<Digit>()) == align_of::<Self>()) as usize - 1)
    ;

    /// The significant digits of the number (little-endian).
    fn significant_digits(&self) -> &[Digit] {
        let l = self.iter()
            .enumerate().rev()
            .find(|(_, &x)| x != 0)
            .map(|(i, _)| i + 1)
            .unwrap_or(0);
        &self[..l]
    }

    /// The last non-zero digit of the number.
    fn leading_digit(&self) -> Option<Digit> {
        self.iter()
            .rev()
            .find(|&&x| x != 0)
            .copied()
    }

    /// Embed in number with `D + E` digits, if possible.
    ///
    /// Not expressable as `TryInto`, as it would clash with blanket implementations,
    /// e.g. for Unsigned<X> with D = X.
    fn to_unsigned<const D: usize, const E: usize>(&self) -> Result<Unsigned<D, E>> {
        let digits = self.significant_digits();
        if digits.len() <= D + E {
            Ok(Unsigned::<D, E>::from_slice(digits))
        } else {
            Err(Error)
        }
    }

    ///// Panics iff [`Self::try_to_unsigned`] fails.
    /////
    ///// Internal use of this embedding of abstract `Number`s in `Unsigned`s never
    ///// actually panics, bar implementation errors.
    //fn to_unsigned<const D: usize, const E: usize>(&self) -> Unsigned<D, E> {
    //    self.try_to_unsigned().unwrap()
    //}

    fn zero() -> Self {
        Self::default()
    }

    fn is_zero(&self) -> bool {
        self.significant_digits().is_empty()
    }

    fn is_one(&self) -> bool {
        self.is_digit() && self[0] == 1
    }

    fn is_digit(&self) -> bool {
        self.significant_digits().len() <= 1
    }

    fn is_odd(&self) -> bool {
        self.get(0).map(|&x| x & 1 != 0).unwrap_or(false)
    }

    /// This is *little endian* ordering, as opposed to the default
    /// ordering on arrays and slices!
    ///
    /// In other words, we start comparing at the leading digits.
    fn cmp(&self, other: &impl Number) -> Ordering {
        let l = self.significant_digits();
        let r = other.significant_digits();

        // #[cfg(test)]
        // println!("lhs has {}, rhs has {}", l.len(), r.len());
        // #[cfg(test)]
        // println!("lhs = {:x?}", &l);
        // #[cfg(test)]
        // println!("rhs = {:x?}", &r);

        match l.len().cmp(&r.len()) {
            Ordering::Equal => {}
            not_equal => return not_equal,
        }

        for (x, y) in l.iter().zip(r.iter()).rev() {
            match x.cmp(&y) {
                Ordering::Equal => (),
                not_equal => return not_equal,
            }
        }

        Ordering::Equal
    }

    fn eq(&self, other: &impl Number) -> bool {
        self.significant_digits() == other.significant_digits()
    }

    fn deref(&self) -> &[Digit] {
        unsafe { core::slice::from_raw_parts(self as *const _ as _, Self::DIGITS) }
    }

    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { core::slice::from_raw_parts_mut(self as *mut _ as _, Self::DIGITS) }
    }

}

// Fails to compile!
//
// #[derive(Clone, Debug, Default)]
// pub struct Fake(u16);
// impl Deref for Fake {
//     type Target = [Digit];
//     fn deref(&self) -> &Self::Target {
//         Number::deref(self)
//     }
// }
// impl Number for Fake {}


/// Mutable access to a [`Number`].
pub trait NumberMut: Number + DerefMut {

    fn from_slice(slice: &[Digit]) -> Self {
        // repeat implementation, so errors show the incompatible slice lengths.
        let mut owned = Self::default();
        owned[..slice.len()].copy_from_slice(slice);
        owned
    }

    fn try_from_slice(slice: &[Digit]) -> Result<Self> {
        if slice.len() > Self::DIGITS {
            Err(Error)
        } else {
            let mut owned = Self::default();
            owned[..slice.len()].copy_from_slice(slice);
            Ok(owned)
        }
    }

    fn from_bytes(bytes: &[u8]) -> Self {
        debug_assert!(Self::BITS >= 8*bytes.len());

        let mut owned = Self::default();
        let owned_bytes: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(&mut owned[0] as *mut _ as _, Self::BITS / 8) };

        let offset = owned_bytes.len() - bytes.len();
        owned_bytes[offset..].copy_from_slice(bytes);

        let mut reversed = Self::default();
        let l = owned.len();
        for i in 0..l {
            reversed[Self::DIGITS - i - 1] = Digit::from_be(owned[i]);
        }

        reversed
    }

    fn set_zero(&mut self) {
        self.fill(0)
    }

    fn one() -> Self {
        let mut one = Self::default();
        one[0] = 1;
        one
    }

    /// Swap endianness of digits in Self and, if the platform is little-endian,
    /// endianness of bytes within digits.
    fn swap_order(self) -> Self {
        let mut swapped = Self::zero();

        let l = self.len();
        for i in 0..l {
            // "On big endian this is a no-op. On little endian the bytes are swapped."
            swapped[l - i - 1] = Digit::from_be(swapped[i]);
        }

        swapped
    }

}

// /// This datum has multiple limbs, and they're all differently sized ;)
// /// All the same, its digits have an order: $[a_0, a_1,... a_{A-1}, b_0, ... c_{C - 1}]$.
// pub struct Limbs<const A: usize, const B: usize, const C: usize, const D: usize> {
//     a: [Digit; A],
//     b: [Digit; B],
//     c: [Digit; C],
//     d: [Digit; D],
// }

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

unsafe impl<const D: usize, const E: usize> Number for Unsigned<D, E> {}
impl<const D: usize, const E: usize> NumberMut for Unsigned<D, E> {}

unsafe impl<const D: usize, const E: usize, const L: usize> Number for Array<D, E, L> {}
impl<const D: usize, const E: usize, const L: usize> NumberMut for Array<D, E, L> {}

/// ## Trait methods as inherent methods, for convenience.
impl<const D: usize, const E: usize, const L: usize> Array<D, E, L> {
    pub fn from_slice(slice: &[Digit]) -> Self {
        NumberMut::from_slice(slice)
    }
    pub fn try_from_slice(slice: &[Digit]) -> Result<Self> {
        NumberMut::try_from_slice(slice)
    }
    pub fn leading_digit(&self) -> Option<Digit> {
        Number::leading_digit(self)
    }
    pub fn significant_digits(&self) -> &[Digit] {
        Number::significant_digits(self)
    }
    pub fn to_unsigned<const M: usize, const N: usize>(&self) -> Result<Unsigned<M, N>> {
        Number::to_unsigned(self)
    }
}

/// Fails for D + E = 0, bound not expressable.
impl<const D: usize, const E: usize> From<Digit> for Unsigned<D, E> {
    fn from(digit: Digit) -> Self {
        let mut r = Self::default();
        r[0] = digit;
        r
    }
}

impl Short<1> {
    /// `const` implementation
    pub const fn from_digit(digit: Digit) -> Self {
        Self { lo: [digit], hi: [] }
    }

    pub const fn digit(&self) -> Digit {
        self.lo[0]
    }
}

impl<const D: usize, const E: usize> From<[Digit; D]> for Unsigned<D, E> {
    fn from(unsigned: [Digit; D]) -> Self {
        Self { lo: unsigned, hi: [0; E] }
    }
}

/// Representation of [`Unsigned`] as big-endian bytes.
///
/// `RefCast` is *not* what we want, as &BigEndian is big-endian, unlike &Unsigned which is
/// little-endian!
///
/// Maybe rename to `BigEndianBytes`
#[repr(transparent)]
#[derive(Default)]
// #[derive(RefCast)]
pub struct BigEndian<const D: usize, const E: usize, const L: usize>(Array<D, E, L>);

// #[repr(transparent)]
// // #[derive(RefCast)]
// pub struct BigEndianArray<const D: usize, const E: usize, const L: usize>(Array<D, E, L>);

impl<const D: usize, const E: usize, const L: usize> Deref for BigEndian<D, E, L> {
    type Target = [u8];
    fn deref(&self) -> &Self::Target {
        unsafe { core::slice::from_raw_parts(self.0.as_ptr() as _, core::mem::size_of::<Self>()) }
    }
}

impl<const D: usize, const E: usize, const L: usize> DerefMut for BigEndian<D, E, L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { core::slice::from_raw_parts_mut(self.0.as_mut_ptr() as _, core::mem::size_of::<Self>()) }
    }
}

impl<const D: usize, const E: usize, const L: usize> BigEndian<D, E, L> {
    fn _from_slice(slice: &[u8]) -> Self {
        // repeat implementation, so errors show the incompatible slice lengths.
        let mut owned = Self::default();
        owned[..slice.len()].copy_from_slice(slice);
        owned
    }
}


// impl<const D: usize, const E: usize> BigEndian<D, E> {
//     /// TODO: consider truncating leading zero bytes (needs some pointer arithmetique)
//     pub fn as_be_bytes(&self) -> &[u8] {
//         unsafe { core::slice::from_raw_parts(&self.0[0] as *const Digit as _, core::mem::size_of::<Digit>() * (D + E)) }
//     }
// }

// impl<const D: usize, const E: usize, const L: usize> BigEndianArray<D, E, L> {
//     /// TODO: consider truncating leading zero bytes (needs some pointer arithmetique)
//     pub fn as_be_bytes(&self) -> &[u8] {
//         unsafe { core::slice::from_raw_parts(&self.0[0] as *const Digit as _, core::mem::size_of::<Digit>() * (D + E) * L) }
//     }
// }

// c'tors and such
impl<const D: usize, const E: usize> Unsigned<D, E> {
    /// Return buffer that dereferences as big-endian bytes.
    pub fn to_bytes(&self) -> BigEndian<D, E, 1> {
        // BigEndian::from_slice(&self.clone().swap_order())

        let mut big_endian = BigEndian(Array::zero());
        // we need to store word such that it bytes are big-endian, whatever
        // the native architecture (although PC/Cortex are both little-endian).
        let l = self.len();
        for i in 0..l {
            // "On big endian this is a no-op. On little endian the bytes are swapped."
            big_endian.0[Self::DIGITS - i - 1] = Digit::from_be(self[i]);
        }
        big_endian
    }
}

impl<const D: usize, const E: usize, const L: usize> Array<D, E, L> {
    /// Return buffer that dereferences as big-endian bytes.
    pub fn to_bytes(&self) -> BigEndian<D, E, L> {
        let mut big_endian = BigEndian(Array::zero());
        // we need to store word such that it bytes are big-endian, whatever
        // the native architecture (although PC/Cortex are both little-endian).
        let l = self.len();
        for i in 0..l {
            // "On big endian this is a no-op. On little endian the bytes are swapped."
            big_endian.0[Self::DIGITS - i - 1] = Digit::from_be(self[i]);
        }
        big_endian
    }
}

impl<const D: usize, const E: usize, const L: usize> BigEndian<D, E, L> {
    const CAPACITY: usize = L * (D + E);

    pub fn trimmed(&self) -> &[u8] {
        let offset = self.iter()
            .enumerate()
            .find(|(_, &x)| x != 0)
            .map(|(i, _)| i)
            .unwrap_or(Self::CAPACITY);
        &self[offset..]
    }
}

/// ## Trait methods as inherent methods, for convenience.
impl<const D: usize, const E: usize> Unsigned<D, E> {
    pub fn from_slice(slice: &[Digit]) -> Self {
        NumberMut::from_slice(slice)
    }
    pub fn try_from_slice(slice: &[Digit]) -> Result<Self> {
        NumberMut::try_from_slice(slice)
    }
    pub fn leading_digit(&self) -> Option<Digit> {
        Number::leading_digit(self)
    }
    pub fn significant_digits(&self) -> &[Digit] {
        Number::significant_digits(self)
    }
    pub fn to_unsigned<const M: usize, const N: usize>(&self) -> Result<Unsigned<M, N>> {
        Number::to_unsigned(self)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[cfg(all(feature = "u32", not(feature = "hex-debug")))]
    fn debug() {
        let u = Short::from([0x76543210, 0xFEDCBA98]);
        assert_eq!(format!("{:X?}", u), "[FE, DC, BA, 98, 76, 54, 32, 10]");
    }

    #[test]
    #[cfg(all(feature = "u32", feature = "hex-debug"))]
    fn debug() {
        let u = Short::from([0x76543210, 0xFEDCBA98]);
        assert_eq!(format!("{:X?}", u), "FEDCBA9876543210");
    }

    #[test]
    fn big_endian() {
        let some_bytes = hex_literal::hex!("cd58cd8accf2db4c839d2553116bef81f0292b4e2d2b3f7df0e5dc8a0721398f");
        let x = Short::<8>::from_bytes(&some_bytes);
        assert_eq!(x.to_bytes().trimmed(), some_bytes);
        let x = Short::<9>::from_bytes(&some_bytes);
        assert_eq!(x.to_bytes().trimmed(), some_bytes);
    }

    #[test]
    fn len() {
        let mut x = Short::from([0,1,0,2,0,0]);
        assert_eq!(x.significant_digits(), &[0,1,0,2]);
        assert_eq!(x.significant_digits().len(), 4);

        x[4] = 3;
        assert_eq!(x.significant_digits().len(), 5);

        let x = Short::from([0, 0, 0]);
        assert_eq!(x.significant_digits().len(), 0);
    }

    #[test]
    #[cfg(feature = "u32")]
    fn partial_eq() {
        use core::convert::TryFrom;
        let d = (1 as Digit) << 31;
        let p = Prime(Convenient::try_from(Short::from([17, d])).unwrap());
        let u = Short::from([17, d]);
        assert_eq!(**p, u);
    }

    #[test]
    fn array() {
        let prod = Array { lo: [[1,2,3]], hi: [[4,5,6]] };
        assert_eq!(prod.significant_digits().len(), 6);
        assert_eq!(prod.significant_digits(), &[1,2,3,4,5,6]);
    }

    // #[test]
    // fn unsigned_carry() {
    //     let uc = UnsignedCarry::from_array_and_carry([1,2,3], 4);
    //     assert_eq!(uc.words(), &[1,2,3,4]);
    // }
}
