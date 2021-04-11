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

use core::{cmp::Ordering, ops::{Deref, DerefMut}};

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
}

// pub type Unsigned<const D: usize, const E: usize> = Array<D, E, 1>;

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

impl <const D: usize> Product<D, 0> {
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
/// this slice must be of length `Self::CAPACITY`.
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
pub unsafe trait Number: Deref<Target = [Digit]> + Clone + core::fmt::Debug + Default { // + PartialEq + PartialOrd {

    const CAPACITY: usize;

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
    fn try_into_unsigned<const D: usize, const E: usize>(&self) -> Result<Unsigned<D, E>> {
        let digits = self.significant_digits();
        if digits.len() <= D + E {
            Ok(Unsigned::<D, E>::from_slice(digits))
        } else {
            Err(Error)
        }
    }

    /// Panics iff [`Self::try_into_unsigned`] fails.
    ///
    /// Internal use of this embedding of abstract `Number`s in `Unsigned`s never
    /// actually panics, bar implementation errors.
    fn to_unsigned<const D: usize, const E: usize>(&self) -> Unsigned<D, E> {
        self.try_into_unsigned().unwrap()
    }

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
        unsafe { core::slice::from_raw_parts(self as *const _ as _, Self::CAPACITY) }
    }

    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { core::slice::from_raw_parts_mut(self as *mut _ as _, Self::CAPACITY) }
    }

}

/// Mutable access to a [`Number`].
pub trait NumberMut: Number + DerefMut {

    fn from_slice(slice: &[Digit]) -> Self {
        // repeat implementation, so errors show the incompatible slice lengths.
        let mut owned = Self::default();
        owned[..slice.len()].copy_from_slice(slice);
        owned
    }

    fn try_from_slice(slice: &[Digit]) -> Result<Self> {
        if slice.len() > Self::CAPACITY {
            Err(Error)
        } else {
            let mut owned = Self::default();
            owned[..slice.len()].copy_from_slice(slice);
            Ok(owned)
        }
    }

    fn set_zero(&mut self) {
        self.fill(0)
    }

    fn one() -> Self {
        let mut one = Self::default();
        one[0] = 1;
        one
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

unsafe impl<const D: usize, const E: usize> Number for Unsigned<D, E> {
    const CAPACITY: usize = D + E;
}

impl<const D: usize, const E: usize> NumberMut for Unsigned<D, E> {}

unsafe impl<const D: usize, const E: usize, const L: usize> Number for Array<D, E, L> {
    const CAPACITY: usize = (D + E)*L;
}

impl<const D: usize, const E: usize, const L: usize> NumberMut for Array<D, E, L> {}

// /// ## Trait methods as inherent methods, for convenience.
// impl<const D: usize, const E: usize, const L: usize> Array<D, E, L> {
//     pub fn from_slice(slice: &[Digit]) -> Self {
//         NumberMut::from_slice(slice)
//     }
//     pub fn try_from_slice(slice: &[Digit]) -> Result<Self> {
//         NumberMut::try_from_slice(slice)
//     }
//     pub fn leading_digit(&self) -> Option<Digit> {
//         Number::leading_digit(self)
//     }
//     pub fn try_into_unsigned<const M: usize, const N: usize>(&self) -> Result<Unsigned<M, N>> {
//         Number::try_into_unsigned(self)
//     }
//     pub fn into_unsigned<const M: usize, const N: usize>(&self) -> Unsigned<M, N> {
//         Number::into_unsigned(self)
//     }
// }

/// Fails for D + E = 0, bound not expressable.
impl<const D: usize, const E: usize> From<Digit> for Unsigned<D, E> {
    fn from(unsigned: Digit) -> Self {
        let mut r = Self::default();
        r[0] = unsigned;
        r
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
// #[derive(RefCast)]
pub struct BigEndian<const D: usize, const E: usize>(Unsigned<D, E>);

#[repr(transparent)]
// #[derive(RefCast)]
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
    pub fn to_be_bytes(&self) -> BigEndian<D, E> {
        let mut big_endian = BigEndian(Unsigned::zero());
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
    pub fn to_be_bytes(&self) -> BigEndianArray<D, E, L> {
        let mut big_endian = BigEndianArray(Array::zero());
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

// /// ## Trait methods as inherent methods, for convenience.
// impl<const D: usize, const E: usize> Unsigned<D, E> {
//     pub fn from_slice(slice: &[Digit]) -> Self {
//         NumberMut::from_slice(slice)
//     }
//     pub fn try_from_slice(slice: &[Digit]) -> Result<Self> {
//         NumberMut::try_from_slice(slice)
//     }
//     pub fn leading_digit(&self) -> Option<Digit> {
//         Number::leading_digit(self)
//     }
//     pub fn significant_digits(&self) -> &[Digit] {
//         Number::significant_digits(self)
//     }
//     pub fn try_into_unsigned<const M: usize, const N: usize>(&self) -> Result<Unsigned<M, N>> {
//         Number::try_into_unsigned(self)
//     }
//     pub fn into_unsigned<const M: usize, const N: usize>(&self) -> Unsigned<M, N> {
//         Number::into_unsigned(self)
//     }
// }

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
        assert_eq!(x.significant_digits(), &[0,1,0,2]);
        assert_eq!(x.significant_digits().len(), 4);

        x[4] = 3;
        assert_eq!(x.significant_digits().len(), 5);

        let x = Short::from([0, 0, 0]);
        assert_eq!(x.significant_digits().len(), 0);
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
