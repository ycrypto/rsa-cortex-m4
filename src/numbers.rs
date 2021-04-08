//! Specification of "big integer" types, specialized to our (allocation-free) purposes.
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

use core::ops::{Deref, DerefMut};

use ref_cast::RefCast;
use zeroize::Zeroize;

use crate::{Digit, Error, Result};

mod trait_implementations;


/// The unstable `{number}::BITS` implementations.
///
/// Cf. <https://github.com/rust-lang/rust/pull/76492>.
pub trait Bits {
    const BITS: usize;
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
    cached_len: Option<usize>,
}

// pub struct MultiDual<const D: usize, const E: usize, const L: usize>([Dual<D, E>; L]);

#[repr(transparent)]
#[derive(RefCast)]
pub struct Odd<const D: usize, const E: usize>(pub(crate) Unsigned<D, E>);

#[repr(transparent)]
#[derive(RefCast)]
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
pub struct Convenient<const D: usize, const E: usize>(Odd<D, E>);

#[repr(transparent)]
#[derive(RefCast)]
/// Prime number (passing primality tests); convenient by definition.
pub struct Prime<const P: usize>(Convenient<P, 0>);

// unsafe impl<const D: usize, const E: usize> Number for Odd<D, E> {
//     fn len(&self) -> usize {
//         self.0.len()
//     }
// }

/// [`Unsigned`] with equal limbs (e.g., public key). If only we had `[T; 2*D]`...
pub type Long<const D: usize> = Unsigned<D, D>;  // duplex with equal limb size
/// [`Unsigned`] with only one limb (e.g., private prime). Short only in comparison to [`Long`].
pub type Short<const D: usize> = Unsigned<D, 0>;  // duplex with empty hi limb

#[repr(C)]
#[derive(Clone, Eq/*, Zeroize*/)]
/// Array of [`Unsigned`].
pub struct Array<const D: usize, const E: usize, const L: usize> {
    lo: [Limb<D>; L],
    hi: [Limb<E>; L],
    cached_len: Option<usize>,
}

// double duplex?
/// Big enough to fit the product of two [`Unsigned`].
pub type Product<const D: usize, const E: usize> = Array<D, E, 2>;

// pub type Long<const D: usize> = MultiUnsigned<D, D, 2>;

// Mul: Unsigned<D> * Unsigned<D> -> Long<D>
//      Short<D> * Short<D> -> MultiUnsigned<D, 0, 2> ~ MultiUnsigned<D, D, 1> = Unsigned<D>
//
// generally, Mul: MultiUnsigned<D, E, 1> * MultiUnsigned<D, E, 1> -> MultiUnsigned<D, E, 2>
// for D = E --> Unsigned<D> * Unsigned<D> ->
//
//  impl From<MultiUnsigned<D, 0, 2>> for MultiUnsigned<D, D, 1>  // aka From<
//  impl From<MultiUnsigned<D, D, 1>> for MultiUnsigned<D, 0, 2>

// pub struct Long<const D: usize, const E: usize>([Unsigned<D, E>; 2]);

// pub type TwoLimbs<const A: usize, const B: usize> = Limbs<A,B,0,0>;
// pub type OneLimb<const A: usize> = Limbs<A,0,0,0>;

// pub type Long<const D: usize> = Limbs<D, 4>;
// pub type Unsigned<const D: usize> = Limbs<D, 2>;
// pub type Short<const D: usize> = Limbs<D, 1>;


/// Something similar to a `Vec<u32>`, without allocations.
///
/// Implementation ***must ensure***:
/// - `self.len() == self.number().len()`
/// - `self.capacity() == self.number_mut().len()`
/// - `Deref` coincides with `self.number()`
/// - `DerefMut` coincides with `self.padded_number_mut()`
///
/// It may or may not be the case that having Deref/DerefMut of
/// different length is too cute (cf. remarks on `NumberMut::invalidate_len`),
/// but it's terribly convenient:
///
/// There is no need to "extend" the allocation, simply write to
/// the desired index / slice (via DerefMut).
///
/// For efficiency, our implementations track (cache) `len`.
///
/// The highest non-zero term determines the leading digit and the length.
///
/// Current implementations are (with const generic usize parameters):
/// - `Unsigned<D, E>`
/// - `Array<D, E, L>`
///
/// Of actual interest are Long (=Unsigned<D,D>) and Short (=Unsigned<D,)>) numbers,
/// where "Short" is tongue-in-cheek.
///
/// A lot of this dance could be skipped if only sums of const generic usizes were
/// considered const (which they are not in Rust 1.51's `min_const_generics`.
///
/// All we really want is to have two "Short" primes $P, Q$, and their "Long" product $N = PQ$.
//pub unsafe trait AsNormalizedLittleEndianWords: Deref<Target = [u32]> + DerefMut {

//    const CAPACITY: usize;

//    fn len(&self) -> usize;

//    fn cache_len(&mut self) -> usize;
//    fn invalidate_len(&mut self);

//    fn capacity() -> usize {
//        Self::CAPACITY
//    }

//    /// Default implementation assumes "data slice" starts at object address.
//    fn words(&self) -> &[u32] {
//        let l = self.len();
//        unsafe { core::slice::from_raw_parts_mut(self as *const _ as _, l) }
//    }

//    /// Default implementation assumes "data slice" starts at object address.
//    fn words_mut(&mut self) -> &mut [u32] {
//        self.invalidate_len();
//        let l = Self::capacity();
//        unsafe { core::slice::from_raw_parts_mut(self as *mut _ as _, l) }
//    }

//    fn leading_digit(&self) -> Option<Digit> {
//        self.last().map(|&d| d)
//    }

//    /// Embed in array of capacity C, if possible.
//    ///
//    /// Fails: iff `self.len() > C`.
//    ///
//    /// Not expressable as `TryInto`, as it would clash with blanket implementations,
//    /// e.g. for Unsigned<L> with C = L.
//    fn try_into_unsigned<const C: usize>(&self) -> Result<Unsigned<C>> {
//        let l = self.len();
//        if l <= C {
//            Ok(Unsigned::<C>::from_slice(&self))
//        } else {
//            Err(Error)
//        }
//    }

//    /// Panics if `try_into_unsigned` fails.
//    fn into_unsigned<const C: usize>(&self) -> Unsigned<C> {
//        self.try_into_unsigned().unwrap()
//    }

//}

pub unsafe trait Number: Deref<Target = [Digit]> + core::fmt::Debug { //+ One + Zero + PartialEq + PartialOrd {

    const CAPACITY: usize;

    #[inline]
    fn capacity() -> usize {
        Self::CAPACITY
    }

    /// The length of the number in terms of relevant digits.
    ///
    /// Example: [0, 1, 0, 2, 0, 0, 0, 0] has length 4.
    fn len(&self) -> usize;

    /// Default implementation assumes "data slice" starts at object address.
    fn number(&self) -> &[Digit] {
        let l = self.len();
        unsafe { core::slice::from_raw_parts_mut(self as *const _ as _, l) }
    }

    /// Default implementation assumes "data slice" starts at object address.
    fn padded_number(&self) -> &[Digit] {
        let l = Self::capacity();
        unsafe { core::slice::from_raw_parts_mut(self as *const _ as _, l) }
    }

    fn leading_digit(&self) -> Option<Digit> {
        self.last().map(|&d| d)
    }

    /// Embed in number with D digits, if possible.
    ///
    /// Fails: iff `self.len() > D + E`.
    ///
    /// Not expressable as `TryInto`, as it would clash with blanket implementations,
    /// e.g. for Unsigned<X> with D = X.
    fn try_into_unsigned<const D: usize, const E: usize>(&self) -> Result<Unsigned<D, E>> {
        let l = self.len();
        if l <= D + E {
            Ok(Unsigned::<D, E>::from_slice(&self))
        } else {
            Err(Error)
        }
    }

    /// Panics iff [`Self::try_into_unsigned`] fails.
    ///
    /// Internal use of this embedding of abstract `Number`s in `Unsigned`s never
    /// actually panics, bar implementation errors.
    fn into_unsigned<const D: usize, const E: usize>(&self) -> Unsigned<D, E> {
        self.try_into_unsigned().unwrap()
    }

    fn is_odd(&self) -> bool {
        if self.len() == 0 {
            return false
        }
        // odd
        if self.number()[0] & 1 == 0 {
            return false
        }
        true
    }

}

// unsafe impl <T> Number for &T
// where
//     T: Number,
//     for<'a> &'a T: <&T as Deref>::Target = [u32],
// {}

/// Mutable access to a [`Number`].
pub trait NumberMut: Number + DerefMut {

    /// Opportunity to cache length, so Number::len (and the Derefs) are more efficient.
    ///
    /// Implementations can NOP this in principle.
    fn cache_len(&mut self) -> usize;

    /// Any mutation should call this method (as a change of what is the leading digit
    /// invalidates the length).
    ///
    /// This is an unsoundness hole, really - the DerefMut which calls `number_mut` (which
    /// calls this) is not the only way to invalidate cached lengths.
    fn invalidate_len(&mut self);

    /// Default implementation assumes "data slice" starts at object address.
    fn number_mut(&mut self) -> &mut [Digit] {
        self.invalidate_len();
        let l = self.len();
        unsafe { core::slice::from_raw_parts_mut(self as *mut _ as _, l) }
    }

    /// Default implementation assumes "data slice" starts at object address.
    fn padded_number_mut(&mut self) -> &mut [Digit] {
        self.invalidate_len();
        let l = Self::capacity();
        unsafe { core::slice::from_raw_parts_mut(self as *mut _ as _, l) }
    }

}

// pub trait NumberComplete: Number + Clone + One + Zero + FromSlice + PartialOrd {}

/// Construction of a [`Number`] from a slice.
///
/// Separate trait so we can give a default implementation.
pub trait FromSlice: NumberMut + Zero {
    fn from_slice(slice: &[Digit]) -> Self {
        let mut owned = Self::zero();
        owned[..slice.len()].copy_from_slice(slice);
        owned.cache_len();
        owned
    }
}

impl<const D: usize, const E: usize> FromSlice for Unsigned<D, E> {}
impl<const D: usize, const E: usize, const L: usize> FromSlice for Array<D, E, L> {}

// impl FromSlice for NumberMut {

//     fn from_slice(slice: &[Digit]) -> Self {
//         let mut owned = Self::zero();
//         owned[..slice.len()].copy_from_slice(slice);
//         owned.cache_len();
//         owned
//     }
// }

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

///// Unsigned integer with `L` digits (L for length).
/////
///// Internal representation as little-endian.
/////
///// TODO: unify terminology (digits vs limbs)
/////
///// In our "heapless" situation, we have no multiplication nor addition.
// #[derive(Clone, Eq, Zeroize)]
// pub struct Unsigned<const L: usize>(Vec<Digit, L>);
// pub struct Unsigned<const L: usize>(pub(crate) [Digit; L]);
// pub type Unsigned<const L: usize> = Product<L, 0>;

// unsafe impl<const L: usize> AsNormalizedLittleEndianWords for Unsigned<L> {
//     const CAPACITY: usize = L;

//     /// 0 if zero, else index + 1 of last non-zero digit
//     fn len(&self) -> usize {
//         self.0.iter()
//             .enumerate().rev()
//             .find(|(_, &x)| x != 0)
//             .map(|(i, _)| i + 1)
//             .unwrap_or(0)
//     }
// }

fn used_len(slice: &[Digit]) -> usize {
    slice.iter()
        .enumerate().rev()
        .find(|(_, &x)| x != 0)
        .map(|(i, _)| i + 1)
        .unwrap_or(0)
}

impl<const D: usize, const E: usize> Unsigned<D, E> {

    fn calculate_len(&self) -> usize {
        let l_hi = used_len(&self.hi);
        if l_hi > 0 {
            D + l_hi
        } else {
            used_len(&self.lo)
        }
    }

    // only for debugging
    #[cfg(test)]
    fn has_cached_len(&self) -> bool {
        self.cached_len.is_some()
    }
}

unsafe impl<const D: usize, const E: usize> Number for Unsigned<D, E> {
    const CAPACITY: usize = D + E;

    fn len(&self) -> usize {
        self.cached_len.unwrap_or_else(|| self.calculate_len())
    }
}

impl<const D: usize, const E: usize> NumberMut for Unsigned<D, E> {
    fn cache_len(&mut self) -> usize {
        let l = self.calculate_len();
        self.cached_len = Some(l);
        l
    }

    fn invalidate_len(&mut self) {
        self.cached_len = None
    }
}

impl<const D: usize, const E: usize, const L: usize> Array<D, E, L> {

    fn calculate_len(&self) -> usize {
        let slice = unsafe { core::slice::from_raw_parts_mut(self as *const _ as _, (D + E)*L) };
        used_len(slice)
        // let l_hi = used_len(&self.hi);
        // if l_hi > 0 {
        //     D + l_hi
        // } else {
        //     used_len(&self.lo)
        // }
    }

    // // only for debugging
    // #[cfg(test)]
    // fn has_cached_len(&self) -> bool {
    //     self.cached_len.is_some()
    // }
}

unsafe impl<const D: usize, const E: usize, const L: usize> Number for Array<D, E, L> {
    const CAPACITY: usize = (D + E)*L;

    fn len(&self) -> usize {
        self.cached_len.unwrap_or_else(|| self.calculate_len())
    }
}


impl<const D: usize, const E: usize, const L: usize> NumberMut for Array<D, E, L> {
    fn cache_len(&mut self) -> usize {
        let l = self.calculate_len();
        self.cached_len = Some(l);
        l
    }

    fn invalidate_len(&mut self) {
        self.cached_len = None
    }
}

// unsafe impl<const M: usize, const N: usize> Number for Unsigned<M, N> {
//     const CAPACITY: usize = M + N;

//     fn len(&self) -> usize {
//         self.l.unwrap_or_else(|| self.calculate_len())
//     }

//     fn cache_len(&mut self) -> usize {
//         let l = self.calculate_len();
//         self.l = Some(l);
//         l
//     }

//     fn invalidate_len(&mut self) {
//         self.l = None
//     }
// }

/// Fails for D + E = 0, bound not expressable.
impl<const D: usize, const E: usize> From<Digit> for Unsigned<D, E> {
    fn from(unsigned: Digit) -> Self {
        let mut r = Self::default();
        r[0] = unsigned;
        // could just set if unsigned != 0
        r.cached_len = Some(if unsigned != 0 {1} else {0});
        r
    }
}

impl<const D: usize, const E: usize> From<[Digit; D]> for Unsigned<D, E> {
    fn from(unsigned: [Digit; D]) -> Self {
        let mut result = Self { lo: unsigned, hi: [0; E], cached_len: None };
        result.cache_len();
        result
    }
}

/// Representation of [`Unsigned`] as big-endian bytes.
#[repr(transparent)]
#[derive(RefCast)]
pub struct BigEndian<const D: usize, const E: usize>(Unsigned<D, E>);

#[repr(transparent)]
#[derive(RefCast)]
pub struct BigEndianArray<const D: usize, const E: usize, const L: usize>(Array<D, E, L>);

impl<const D: usize, const E: usize> BigEndian<D, E> {
    /// TODO: consider truncating leading zero bytes (needs some pointer arithmetique)
    pub fn as_be_bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(&self.0[0] as *const Digit as _, core::mem::size_of::<Digit>() * (D + E)) }
    }
}

impl<const D: usize, const E: usize, const L: usize> BigEndianArray<D, E, L> {
    /// TODO: consider truncating leading zero bytes (needs some pointer arithmetique)
    pub fn as_be_bytes(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(&self.0[0] as *const Digit as _, core::mem::size_of::<Digit>() * (D + E) * L) }
    }
}

// c'tors and such
impl<const D: usize, const E: usize> Unsigned<D, E> {
    /// TODO: consider `into_be_bytes`, reusing the buffer.
    ///
    /// i.e.
    /// - swap words + endianness on self.0
    /// - return BigEndian(self.0)
    fn to_be_bytes(&self) -> BigEndian<D, E> {
        let mut big_endian = BigEndian(Zero::zero());
        // we need to store word such that it bytes are big-endian, whatever
        // the native architecture (although PC/Cortex are both little-endian).
        let l = self.len();
        for i in 0..l {
            // "On big endian this is a no-op. On little endian the bytes are swapped."
            big_endian.0[Self::CAPACITY - i - 1] = Digit::from_be(self[i]);
        }
        big_endian
    }
}

impl<const D: usize, const E: usize, const L: usize> Array<D, E, L> {
    /// TODO: consider `into_be_bytes`, reusing the buffer.
    ///
    /// i.e.
    /// - swap words + endianness on self.0
    /// - return BigEndian(self.0)
    fn to_be_bytes(&self) -> BigEndianArray<D, E, L> {
        let mut big_endian = BigEndianArray(Zero::zero());
        // we need to store word such that it bytes are big-endian, whatever
        // the native architecture (although PC/Cortex are both little-endian).
        let l = self.len();
        for i in 0..l {
            // "On big endian this is a no-op. On little endian the bytes are swapped."
            big_endian.0[Self::CAPACITY - i - 1] = Digit::from_be(self[i]);
        }
        big_endian
    }
}

// /// Trait methods as inherent methods, for convenience.
// impl<const L: usize> Unsigned<L> {
//     pub fn from_slice(slice: &[u32]) -> Self {
//         FromSlice::from_slice(slice)
//     }
//     pub fn leading_digit(&self) -> Option<Digit> {
//         AsNormalizedLittleEndianWords::leading_digit(self)
//     }
//     pub fn try_into_unsigned<const C: usize>(&self) -> Result<Unsigned<C>> {
//         AsNormalizedLittleEndianWords::try_into_unsigned(self)
//     }
//     pub fn into_unsigned<const C: usize>(&self) -> Unsigned<C> {
//         AsNormalizedLittleEndianWords::into_unsigned(self)
//     }
//     pub fn one() -> Self {
//         One::one()
//     }
//     pub fn zero() -> Self {
//         Zero::zero()
//     }
// }


///// Product of two unsigned integers.
/////
///// `Product<M, L>` is what `Unsigned<M + L>` would be, if const-generics on stable
///// would allow expressing this. This is a workaround type.
/////
///// The special case `Product<L, 1>` has an alias `UnsignedCarry<L>`.
// #[repr(C)]
// #[derive(Clone, Eq, Zeroize)]
// pub struct Product<const M: usize, const N: usize> {
//     lo: [u32; M],
//     hi: [u32; N],
//     l: Option<usize>,
// }

// impl<const M: usize, const N: usize> Product<M, N> {

//     fn used_len(slice: &[Digit]) -> usize {
//         slice.iter()
//             .enumerate().rev()
//             .find(|(_, &x)| x != 0)
//             .map(|(i, _)| i + 1)
//             .unwrap_or(0)
//     }

//     fn calculate_len(&self) -> usize {
//         let l_hi = Self::used_len(&self.hi);
//         if l_hi > 0 {
//             M + l_hi
//         } else {
//             Self::used_len(&self.lo)
//         }
//     }

//     fn has_cached_len(&self) -> bool {
//         self.l.is_some()
//     }
// }

/// ## Trait methods as inherent methods, for convenience.
impl<const D: usize, const E: usize> Unsigned<D, E> {
    pub fn from_slice(slice: &[Digit]) -> Self {
        FromSlice::from_slice(slice)
    }
    pub fn leading_digit(&self) -> Option<Digit> {
        Number::leading_digit(self)
    }
    pub fn try_into_unsigned<const M: usize, const N: usize>(&self) -> Result<Unsigned<M, N>> {
        Number::try_into_unsigned(self)
    }
    pub fn into_unsigned<const M: usize, const N: usize>(&self) -> Unsigned<M, N> {
        Number::into_unsigned(self)
    }
    pub fn one() -> Self {
        One::one()
    }
    pub fn zero() -> Self {
        Zero::zero()
    }
}

///// `Unsigned<L + 1>` aka `Product<L, 1>`.
/////
///// Due to limitations in const-generics on stable, we can't express
///// `Unsigned<L + 1>`. This is a workaround type.
//pub type UnsignedCarry<const L: usize> = Product<L, 1>;

//// c'tors and such
//impl<const L: usize> UnsignedCarry<L> {
//    pub fn from_array_and_carry(array: [u32; L], carry: u32) -> Self {
//        let mut result = Self {
//            lo: array,
//            hi:[carry],
//            l: None
//        };
//        result.cache_len();
//        result
//    }
//    pub fn from_slice_and_carry(slice: &[u32], carry: u32) -> Self {
//        let mut array = [0; L];
//        array[..slice.len()].copy_from_slice(slice);
//        Self::from_array_and_carry(array, carry)
//    }
//}

///// `Product<L, L>`
//pub type Square<const L: usize> = Product<L, L>;

///// Unsigned integer that is odd.
/////
///// These are used as moduli.
/////
///// The oddness condition ensures we can use Montgomery multiplication/reduction.
//#[derive(Clone, Debug, Eq, PartialEq, Zeroize)]
//// Q: rename to `Odd`? :)
//pub struct Odd<const L: usize>(pub Unsigned<L>);

///// Odd prime.
//#[derive(Clone, Eq, PartialEq, Zeroize)]
//#[zeroize(drop)]
//pub struct Prime<const L: usize>(pub Odd<L>);

/// $1$
pub trait One: Sized + PartialEq {
    fn one() -> Self;

    fn is_one(&self) -> bool { *self == Self::one() }
    fn set_one(&mut self) { *self = Self::one(); }
}

/// $0$
pub trait Zero: Sized + PartialEq {
    fn zero() -> Self;

    fn is_zero(&self) -> bool { *self == Self::zero() }
    fn set_zero(&mut self) { *self = Self::zero(); }
}

impl One for Digit {
    #[inline]
    fn one() -> Self {
        1
    }
}

// impl<const L: usize> One for Unsigned<L> {
impl<T: NumberMut + Default + PartialEq> One for T {
    fn one() -> Self {
        let mut one = Self::default();
        one[0] = 1;
        one
    }
}

impl Zero for Digit {
    #[inline]
    fn zero() -> Self {
        0
    }
}

impl<T: Number + Default + PartialEq> Zero for T {
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
    #[cfg(target_pointer_width = "32")]
    fn debug() {
        let u = Short::from([0x76543210, 0xFEDCBA98]);
        assert_eq!(format!("{:X?}", u), "[FE, DC, BA, 98, 76, 54, 32, 10]");
    }

    #[test]
    fn len() {
        let mut x = Short::from([0,1,0,2,0,0]);
        assert!(x.has_cached_len());
        assert_eq!(*x, [0,1,0,2]);
        assert!(x.has_cached_len());
        assert_eq!(x.len(), 4);
        assert!(x.has_cached_len());

        x[4] = 3;
        assert!(!x.has_cached_len());
        assert_eq!(x.len(), 5);

        let x = Short::from([0, 0, 0]);
        assert_eq!(x.len(), 0);
    }

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn partial_eq() {
        use core::convert::TryFrom;
        let d = (1 as Digit) << 31;
        let p = Prime(Convenient::try_from(Short::from([17, d])).unwrap());
        let u = Short::from([17, d]);
        assert_eq!(&p.0.0, &u);
    }

    #[test]
    fn array() {
        let prod = Array { lo: [[1,2,3]], hi: [[4,5,6]], cached_len: None };
        assert_eq!(prod.number().len(), 6);
        assert_eq!(prod.number(), &[1,2,3,4,5,6]);
    }

    // #[test]
    // fn unsigned_carry() {
    //     let uc = UnsignedCarry::from_array_and_carry([1,2,3], 4);
    //     assert_eq!(uc.words(), &[1,2,3,4]);
    // }
}