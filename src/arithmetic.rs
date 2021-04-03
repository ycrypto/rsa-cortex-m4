//! BigUnit and ModInt.
//!
//! TODO: Note that we also have use for `Mod(Unsigned<L>, 2^{32*L})`,
//! for instance to calculate `1/e (mod p - 1)`.

#![allow(unstable_name_collisions)]

use core::cmp::Ordering;
use core::{cmp, fmt};
use core::ops::{Add, Div, Mul, Rem, Shl, ShlAssign, Shr, ShrAssign, SubAssign};
use zeroize::Zeroize;

use crate::{Error, Result};

pub type Digit = u32;
pub type DoubleDigit = u64;
pub type SignedDoubleDigit = i64;

trait Bits {
    /// Otherwise compiler complains about potential future collision
    /// (which... we'd realize then and there).
    const BITS: usize;
}

impl Bits for Digit {
    const BITS: usize = 32;
}

impl Bits for DoubleDigit {
    const BITS: usize = 64;
}

/// Basic implementations of standard traits.
mod impls;
// use impls::*;

// /// Guaranteed to have last digit != 0.
// /// Useful for instance to avoid implementing PartialOrd for all possible combinations
// /// of Unsigned and workaround types.
// #[derive(Eq, PartialEq)]
// pub struct NormalizedLittleEndian<'a>(&'a [Digit]);

// #[derive(Eq, PartialEq)]
// pub struct NormalizedLittleEndianMut<'a>(&'a mut [Digit]);

// #[derive(Eq, PartialEq)]
// pub struct NormalizedBigEndian<'a>(&'a [u8]);

// impl NormalizedLittleEndian<'_> {
//     fn len(&self) -> usize {
//         self.0.len()
//     }
// }

/// Implementation must ensure self.len() == self.words().len() and underlying len == self.words_mut().len()
pub unsafe trait AsNormalizedLittleEndianWords {
    fn len(&self) -> usize;
    fn words(&self) -> &[u32]; //NormalizedLittleEndian<'_>;
    fn words_mut(&mut self) -> &mut [u32]; //NormalizedLittleEndianMut<'_>;
}

// pub trait AsNormalizedBigEndianBytes {
//     fn as_be_bytes(&self) -> NormalizedBigEndian<'_>;
// }

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
    /// 0 if zero, else index + 1 of last non-zero digit
    fn len(&self) -> usize {
        self.0.iter()
            .enumerate().rev()
            .find(|(_, &x)| x != 0)
            .map(|(i, _)| i + 1)
            .unwrap_or(0)
    }

    fn words(&self) -> &[u32] {
        let l = self.len();
        &self.0[..l]
    }
    fn words_mut(&mut self) -> &mut [u32] {
        let l = self.len();
        &mut self.0//[..l]
    }
}

impl<const L: usize> Unsigned<L> {
    pub fn from_slice(slice: &[u32]) -> Self {
        let mut x = Self::zero();
        x.0[..slice.len()].copy_from_slice(slice);
        x
    }

    // pub fn as_le_words(&self) -> &[u32],
    //     AsNormalizedLittleEndianWords::as_le_words(self)
    // }

    // pub fn as_le_words_mut(&mut self) -> &[u32],
    //     AsNormalizedLittleEndianWords::as_le_words_mut(self)
    // }

    pub fn leading_digit(&self) -> Option<Digit> {
        self.last().map(|&d| d)
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

    /// Embed in array of size M, if possible.
    ///
    /// This is not an implementation of TryInto (and should maybe be renamed?),
    /// as it clashes with blanket implementations, e.g. for L = M.
    pub fn try_into<const M: usize>(&self) -> Result<Unsigned<M>> {
        let l = self.len();
        if l <= M {
            Ok(Unsigned::<M>::from_slice(&self.words()))
        } else {
            Err(Error)
        }
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

impl<const L: usize> fmt::Debug for Unsigned<L> {
    /// TODO: Do we want debug output to be big-endian bytes (as currently implemented)?
    /// Or stick with internal representation?
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.to_be_bytes().as_be_bytes(), f)
    }
}

/// Unsigned<L + 1>.
///
/// Due to limitations in const-generics on stable, we can't express
/// `Unsigned<L + 1>`. This is a workaround type.
pub type UnsignedCarry<const L: usize> = Product<L, 1>;

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
// pub struct UnsignedCarry<const L: usize> {
//     lo: Unsigned<L>,
//     carry: u32,
// }

// impl<const L: usize> UnsignedCarry<L> {
//     pub fn as_le_words(&self) -> NormalizedLittleEndian<'_> {
//         let l = if self.carry != 0 {
//             L + 1
//         } else {
//             self.lo.len()
//         };
//         NormalizedLittleEndian(unsafe {
//             core::slice::from_raw_parts(&self.lo.0[0], l)
//         })
//     }
// }

/// Square of two unsigned integers.
///
/// Due to limitations in const-generics on stable, we can't express
/// something like `Unsigned<2*L>`. This is a workaround type.
#[repr(C)]
#[derive(Clone, Default, Eq, PartialEq, Zeroize)]
pub struct Product<const M: usize, const N: usize> {
    lo: Unsigned<M>,
    hi: Unsigned<N>,
}

pub type Square<const L: usize> = Product<L, L>;

unsafe impl<const M: usize, const N: usize> AsNormalizedLittleEndianWords for Product<M, N> {
    fn len(&self) -> usize {
        let l_hi = self.hi.len();
        if l_hi > 0 {
            M + l_hi
        } else {
            self.lo.len()
        }
    }

    fn words(&self) -> &[u32]{
        let l = self.len();
        unsafe { core::slice::from_raw_parts(&self.lo.0[0], l) }
    }
    fn words_mut(&mut self) -> &mut [u32] {
        // let l = self.len();
        let l = M + N;
        unsafe { core::slice::from_raw_parts_mut(&mut self.lo.0[0], l) }
    }
}

impl<const M: usize, const N: usize> Product<M, N> {
    pub fn len(&self) -> usize {
        AsNormalizedLittleEndianWords::len(self)
    }

    // pub fn as_le_words(&self) -> NormalizedLittleEndian<'_> {
    //     AsNormalizedLittleEndianWords::as_le_words(self)
    // }
    // pub fn as_le_words_mut(&mut self) -> NormalizedLittleEndianMut<'_> {
    //     AsNormalizedLittleEndianWords::as_le_words_mut(self)
    // }

    pub fn try_into<const L: usize>(&self) -> Result<Unsigned<L>> {
        let l = self.len();
        if l <= L {
            Ok(Unsigned::<L>::from_slice(&self.words()))
        } else {
            Err(Error)
        }
    }
}

// fn prod<const L: unsigned>(a: &Unsigned<L>, b: &Unsigned<L>) -> Square<L> {
// }

pub trait One: Sized + PartialEq {
    fn one() -> Self;

    fn is_one(&self) -> bool { *self == Self::one() }
    fn set_one(&mut self) { *self = Self::one(); }
}

impl<const L: usize> One for Unsigned<L> {
    fn one() -> Self {
        let mut one = Self::default();
        one.0[0] = 1;
        one
    }
}

pub trait Zero: Sized + PartialEq {
    fn zero() -> Self;

    fn is_zero(&self) -> bool { *self == Self::zero() }
    fn set_zero(&mut self) { *self = Self::zero(); }
}

impl<const L: usize> Zero for Unsigned<L> {
    fn zero() -> Self {
        Self::default()
    }
    fn is_zero(&self) -> bool {
        self.len() == 0
    }
}

/// Add trait methods as inherent for convenience.
impl<const L: usize> Unsigned<L> {
    pub fn one() -> Self {
        One::one()
    }
    pub fn zero() -> Self {
        Zero::zero()
    }
}

/// Unsigned integer that is non-zero and odd.
///
/// These are used as moduli.
///
/// The oddness condition ensures we can use Montgomery multiplication/reduction.
#[derive(Clone, Eq, PartialEq, Zeroize)]
pub struct NonZeroOdd<const L: usize>(Unsigned<L>);

/// Odd prime.
#[derive(Clone, Eq, PartialEq, Zeroize)]
#[zeroize(drop)]
pub struct Prime<const L: usize>(NonZeroOdd<L>);

/// Modular integer, corresponds to the residue class "modulo modulus".
///
/// For fixed modulus, this is a ring. If the modulus is prime, this is a field.
///
/// All constructors must enforce that `x < n` is the canonical
/// residue class representative.
///
/// TODO: Maybe x and n don't need to have the same size.
/// E.g., would like to express x mod 2**{32*L}.
/// But nothing actually larger than this.
///
/// On the other hand, if `n` is substantially smaller (e.g., `e`, which has L = 1),
/// then it would be nice to project `x` down to that size.
#[derive(Clone)]
pub struct Modular<'n, const L: usize> {
    x: Unsigned<L>,
    n: &'n NonZeroOdd<L>,
}

impl<const L: usize> Zeroize for Modular<'_, L> {
    fn zeroize(&mut self) {
        self.x.zeroize();
    }
}

impl<const L: usize> Unsigned<L> {
    /// The associated residue class modulo n.
    ///
    /// Note that storage requirements of the residue class are the same
    /// as the modulus (+ reference to it), not the original integer.
    pub fn modulo<const N: usize>(self, n: &NonZeroOdd<N>) -> Modular<'_, N> {
        let reduced_residue_class_representative = &self % &**n;
        Modular { x: reduced_residue_class_representative, n }
        // let mut modular = Modular { x: self, n };
        // reduce_modulo(0, &mut modular.x, n);
        // modular
    }

    /// The canonical representative of the associated residue class modulo n.
    pub fn reduce(self, n: &NonZeroOdd<L>) -> Self {
        self.modulo(n).lift()
    }

}

// pub fn chinese_remainder_theorem

impl<const N: usize> Modular<'_, N> {
    pub fn inverse(&self) -> Self {
        todo!();
    }

    /// The canonical representative of this residue class.
    ///
    /// This is like [`lift`][lift] in GP/PARI
    ///
    /// [lift]: https://pari.math.u-bordeaux.fr/dochtml/html/Conversions_and_similar_elementary_functions_or_commands.html#se:lift
    pub fn lift<const L: usize>(self) -> Unsigned<L> {
        /// TODO: if L < N (or rather, self.modulo.len()), then lift and project maybe? nah
        self.x.try_into().unwrap()
    }

    // pub fn to_the(self, exponent: & impl Into<Unsigned<L>>) -> Self {
    pub fn power(self, exponent: & impl Into<Unsigned<N>>) -> Self {
        todo!();
    }
}

impl<const L: usize> From<Modular<'_, L>> for Unsigned<L> {
    fn from(class: Modular<'_, L>) -> Self {
        class.lift()
    }
}

impl<const L: usize> From<Digit> for Unsigned<L> {
    fn from(unsigned: Digit) -> Self {
        let mut r = Self::default();
        r.0[0] = unsigned;
        r
    }
}

/// Intention is to replace this with the UMAAL assembly instruction on Cortex-M4.
///
/// Operation: `(hi, lo) = m*n + hi + lo`
///
/// This works, because `(2^32 - 1)^2 + 2*(2^32 - 1) = 2^64 - 1`.
pub fn umaal(hi: &mut u32, lo: &mut u32, m: u32, n: u32) {
    let result = ((m as u64) * (n as u64)) + (*hi as u64) + (*lo as u64);
    *hi = (result >> u32::BITS) as u32;
    *lo = result as u32;
}

/// place (a + b + c) in r with carry c
pub fn addc(a: u32, b: u32, c: &mut u32, r: &mut u32) {
    *r = a;
    umaal(c, r, 1, b);
}

fn reduce_modulo_once<const L: usize>(c: Digit, x: &mut Unsigned<L>, n: &NonZeroOdd<L>) {
    todo!();
    // if c > 0 || *x >= *n {
    //     sub_assign_unchecked(x, n);
    // }
}

fn reduce_modulo<const L: usize>(c: Digit, x: &mut Unsigned<L>, n: &NonZeroOdd<L>) {
    todo!();
}

fn add_modulo<const L: usize>(a: &Unsigned<L>, b: &Unsigned<L>, n: &NonZeroOdd<L>) -> Unsigned<L> {
    let mut r = Unsigned::<L>::default();
    let mut c = 0;

    // 1. sum up term-by-term
    for i in 0..L {
        // let sum = (a.0[i] as u64) + (b.0[i] as u64) + c as u64;
        // r.0[i] = sum as u32;
        // c = (sum >> 32) as u32;
        addc(a.0[i], b.0[i], &mut c, &mut r.0[i]);
    }

    // for ((ai, bi), ri) in (a.as_ref().iter().zip(b.as_ref().iter())).zip(r.as_mut().iter()) {
    //     let sum = (*ai as u64) + (*bi as u64) + c as u64;
    //     *ri = sum as u32;
    //     todo!();
    // }

    // 2. reduce modulo n
    reduce_modulo(c, &mut r, n);

    // 3. done
    r
}

impl<'a, 'b, const L: usize> Add<&'b Unsigned<L>> for Modular<'a, L> {
    type Output = Self;

    fn add(self, rhs: &'b Unsigned<L>) -> Self {
        todo!();
    }
}

impl <'l, const L: usize> Mul<&'l Unsigned<L>> for &'l Unsigned<L> {

    type Output = Square<L>;

    /// product-scanning implementation of multiplication
    fn mul(self, other: Self) -> Self::Output {
        let mut product = Square::default();
        let mut accumulator = DoubleDigit::default();

        for k in 0..2*L {
            // TODO: figure out proper loop (although maybe the compiler is smart enough?)
            for i in 0..self.len() {
                for j in 0..other.len() {
                    if i + j == k {
                        accumulator += (self[i] as u64) * (other[j] as u64);
                    }
                }
            }
            product[k] = accumulator as Digit;
            accumulator = accumulator >> Digit::BITS;
        }
        product
    }
}

// impl <'l, const L: usize> Mul<&'l Unsigned<L>> for &'l Unsigned<L> {
//     type Output = Square<L>;
//     fn mul(self, other: Self) -> Self::Output {


// /// Input:  x = (x_0,x_1,...,x_n), n = (n_0,n_1, ...n_t, 0, ...0), 1 <= t <= L, yt != 0
// /// Output: q = (q_0,q_1,...,q_{n-t}), r = (r_0,r_1,...r_t) with x=qy+r, 0<=r<y
// fn div_rem<const L: usize>(x: &mut Unsigned<L>, n: &NonZeroOdd<L>) -> (Unsigned<L>, Unsigned<L>) {
//     let mut q = Unsigned::default();
//     let mut r = Unsigned::default();

//     let t = n.len();

//     (q, r)
// }

/// Divide a two digit numerator by a one digit divisor, returns quotient and remainder:
///
/// Note: the caller must ensure that both the quotient and remainder will fit into a single digit.
/// This is _not_ true for an arbitrary numerator/denominator.
///
/// (This function also matches what the x86 divide instruction does).
///
/// TODO: Not sure this is particularly useful / efficient on Cortex-M4.
///
/// REMARK: This is Knuth's operation c0), "memorizing the multiplication table in reverse."
#[inline]
pub fn div_wide(hi: Digit, lo: Digit, divisor: Digit) -> (Digit, Digit) {
    // // what is the use of this?
    // debug_assert!(hi < divisor);

    let x = ((hi as DoubleDigit) << Digit::BITS) + lo as DoubleDigit;
    let divisor = divisor as DoubleDigit;

    let q = x / divisor;
    debug_assert!(q <= Digit::MAX as _);
    let r = x % divisor;
    debug_assert!(r <= Digit::MAX as _);

    (q as Digit, r as Digit)
}

/// Divides x in-place by digit n, returning the multiple of n and the remaining digit.
pub fn div_rem_assign_digit<const L: usize>(x: &mut Unsigned<L>, n: Digit) -> Digit {
    let mut remainder = 0;

    // run down the digits in x, dividing each by n, while carrying along the remainder
    let l = x.len();
    for digit in x.iter_mut().rev() {
        let (q, r) = div_wide(remainder, *digit, n);
        *digit = q;
        remainder = r;
    }

    remainder
}

// /// Divides x in-place by digit n, returning the multiple of n and the remaining digit.
// pub fn div_rem_digit<const L: usize>(mut x: Unsigned<L>, n: Digit) -> (Unsigned<L>, Digit) {
//     let mut remainder = 0;

//     // run down the digits in x, dividing each by n, while carrying along the remainder
//     let l = x.len();
//     for digit in x.as_le_words_mut().iter_mut().rev() {
//         let (q, r) = div_wide(remainder, *digit, n);
//         *digit = q;
//         remainder = r;
//     }

//     (x, remainder)
// }

impl<const L: usize> ShlAssign<usize> for Unsigned<L> {
    #[inline]
    /// Compared to `num-bigint{,-dig}`, this is a truncating shift.
    ///
    /// We could consider implementing this with Output UnsignedCarry or Square,
    /// if necessary.
    fn shl_assign(&mut self, bits: usize) {
        // biguint_shl(Cow::Owned(self), rhs)

        let l = self.len();
        let n_digits = bits / Digit::BITS;

        let data = &mut self.0;

        // shift back by n_digits
        data.copy_within(..(l - n_digits), n_digits);
        data[..n_digits].fill(0);

        // shift back sub-digit amount of bits
        let n_bits = bits % Digit::BITS;
        if n_bits > 0 {
            let mut carry = 0;
            for elem in data[n_digits..].iter_mut() {
                let new_carry = *elem >> (Digit::BITS - n_bits);
                *elem = (*elem << n_bits) | carry;
                carry = new_carry;
            }
        }
    }
}

impl<const L: usize> Shr<usize> for &Unsigned<L> {
    type Output = Unsigned<L>;

    #[inline]
    fn shr(self, bits: usize) -> Self::Output {
        let mut result = self.clone();
        result >>= bits;
        result
    }
}

impl<const L: usize> ShrAssign<usize> for Unsigned<L> {

    #[inline]
    fn shr_assign(&mut self, bits: usize) {

        let l = self.len();
        let n_digits = bits / Digit::BITS;

        if n_digits >= self.len() {
            self.set_zero();
            return;
        }

        let data = &mut self.0;

        // shift by n_digits
        data.copy_within(n_digits.., n_digits);
        data[(l - n_digits)..].fill(0);

        let n_bits = bits % Digit::BITS;

        if n_bits > 0 {
            let mut borrow = 0;
            for elem in data.iter_mut().rev().skip(n_digits) {
                let new_borrow = *elem << (Digit::BITS - n_bits);
                *elem = (*elem >> n_bits) | borrow;
                borrow = new_borrow;
            }
        }
    }
}

impl<const L: usize> Shl<usize> for &Unsigned<L> {
    type Output = Unsigned<L>;

    #[inline]
    fn shl(self, bits: usize) -> Self::Output {
        let mut result = self.clone();
        result <<= bits;
        result
    }
}

/// Subtract with borrow:
#[inline]
pub fn subb(a: Digit, b: Digit, acc: &mut SignedDoubleDigit) -> Digit {
    *acc += a as SignedDoubleDigit;
    *acc -= b as SignedDoubleDigit;
    let lo = *acc as Digit;
    *acc >>= Digit::BITS;
    lo
}

pub fn sub_assign(a: &mut [Digit], b: &[Digit]) {
    let mut borrow = 0;

    let len = cmp::min(a.len(), b.len());
    let (a_lo, a_hi) = a.split_at_mut(len);
    let (b_lo, b_hi) = b.split_at(len);

    for (a, b) in a_lo.iter_mut().zip(b_lo) {
        *a = subb(*a, *b, &mut borrow);
    }

    if borrow != 0 {
        for a in a_hi {
            *a = subb(*a, 0, &mut borrow);
            if borrow == 0 {
                break;
            }
        }
    }

    // note: we're _required_ to fail on underflow
    assert!(
        borrow == 0 && b_hi.iter().all(|x| *x == 0),
        "Cannot subtract b from a because b is larger than a."
    );
}

impl<const L: usize> SubAssign<&Unsigned<L>> for Unsigned<L> {
    fn sub_assign(&mut self, other: &Unsigned<L>) {
        // todo!();
        sub_assign(&mut self.0, &other.0);
    }
}

// Add with carry:
#[inline]
pub fn adc(a: Digit, b: Digit, acc: &mut DoubleDigit) -> Digit {
    *acc += a as DoubleDigit;
    *acc += b as DoubleDigit;
    let lo = *acc as Digit;
    *acc >>= Digit::BITS;
    lo
}

// our signature:
// pub fn addc(a: u32, b: u32, c: &mut u32, r: &mut u32)

// Only for the Add impl:
#[inline]
pub fn add_assign_carry(a: &mut [Digit], b: &[Digit]) -> Digit {
    debug_assert!(a.len() >= b.len());

    let mut carry = 0;
    let (a_lo, a_hi) = a.split_at_mut(b.len());

    for (a, b) in a_lo.iter_mut().zip(b) {
        *a = adc(*a, *b, &mut carry);
    }

    if carry != 0 {
        for a in a_hi {
            *a = adc(*a, 0, &mut carry);
            if carry == 0 {
                break;
            }
        }
    }

    carry as Digit
}

/// /Two argument addition of raw slices:
/// a += b
///
/// The caller _must_ ensure that a is big enough to store the result - typically this means
/// resizing a to max(a.len(), b.len()) + 1, to fit a possible carry.
pub fn add_assign(a: &mut [Digit], b: &[Digit]) {
    let carry = add_assign_carry(a, b);

    debug_assert!(carry == 0);
}


/// "Multi-precision division of x by n".
///
/// Meaning: Return unique values `(q, r)` with `x = q*n + r`, and `0 <= r < n`.
///
/// To do this in the general case means making quite a few guesses -> this operation is to be used
/// sparingly; there are many tricks available in the literature to avoid it.
///
/// Currently, this copies the implementation in [`num-bigint::biguint::division`][num-bigint].
///
/// [num-bigint]: https://docs.rs/num-bigint/0.4.0/src/num_bigint/biguint/division.rs.html#111-156

// this should really be: (m + n) / n --> ((m + 1), n)
// pub fn div_rem<const M: usize, const N: usize>(x: &Square<M, N>, n: &Unsigned<N>) -> (UnsignedCarry<M>, Unsigned<N>) {

pub fn div_rem<const X: usize, const N: usize>(x: &Unsigned<X>, n: &Unsigned<N>) -> (Unsigned<X>, Unsigned<N>) {
    if n.is_zero() {
        todo!("specialize to `mod 2**{{32*N}}, maybe");
    }
    if x.is_zero() {
        return (Default::default(), Default::default());
    }

    if n.len() == 1 {
        let n = n.0[0];

        let mut div = x.clone();
        if n == 1 {
            return (div, Zero::zero());
        } else {
            let rem = div_rem_assign_digit(&mut div, n);
            return (div, rem.into());
        }
    }

    // let n = n.as_le_words();

    // Required or the q_len calculation below can underflow:
    // match x.as_le_words().cmp(&n.as_le_words()) {
    match x.partial_cmp(n).unwrap() {
        Ordering::Less => return (Zero::zero(), n.clone()),
        Ordering::Equal => return (One::one(), Zero::zero()),
        Ordering::Greater => {} // Do nothing
    }

    // This algorithm is from Knuth, TAOCP vol 2 section 4.3, algorithm D:
    //
    // Shift n to set highest bit (in its leading digit), so the generated guesses are as
    // large as possible in the following loop.
    //
    // This shift has no influence on `q`, and will be reverted for `r` at the end.
    // let shift = n.as_le_words().last().unwrap().leading_zeros() as usize;
    let shift = n.leading_digit().unwrap().leading_zeros() as usize;

    let mut r = x << shift;
    // by the above, x >= n, so `n` and its shift `b` must fit into Unsigned::<X>, as `x` does
    // let b: Unsigned<X> = (n << shift).try_into().unwrap();
    let n: Unsigned<X> = (n << shift).try_into().unwrap();

    // we now want to calculate a/b, in the sense a = qb + r
    // in this sense, a = r (starts at a, goes down to r by removing multiples of b, the
    // multipliers summed into q, which starts at 0)

    // The algorithm works by incrementally calculating "guesses", q0, for part of the
    // remainder. Once we have any number q0 such that q0 * b <= a, we can set
    //
    //     q += q0
    //     a -= q0 * b
    //
    // and then iterate until a < b. Then, (q, a) will be our desired quotient and remainder.
    //
    // q0, our guess, is calculated by dividing the last few digits of a by the last digit of b
    // - this should give us a guess that is "close" to the actual quotient, but is possibly
    // greater than the actual quotient. If q0 * b > a, we simply use iterated subtraction
    // until we have a guess such that q0 * b <= a.

    let q_len = x.len() - n.len() + 1;
    let mut q = Unsigned::<X>::default();

    // We reuse the same temporary to avoid hitting the allocator in our inner loop - this is
    // sized to hold a0 (in the common case; if a particular digit of the quotient is zero a0
    // can be bigger).
    //

    // this is the "trial division" that Montgomery would later refer to :)
    let mut trial = Unsigned::<X>::default(); // SmallVec::with_capacity(2)

    for j in (0..q_len).rev() {
        /*
         * When calculating our next guess q0, we don't need to consider the digits below j
         * + b.len() - 1: we're guessing digit j of the quotient (i.e. q0 << j) from
         * digit bn of the divisor (i.e. bn << (b.data.len() - 1) - so the product of those
         * two numbers will be zero in all digits up to (j + b.data.len() - 1).
         */
        let offset = j + n.len() - 1;
        if offset >= r.len() {
            continue;
        }

        // set "trial" to current remainder, immediately after we divide by highest digit of
        // divisor `n` to get a guess.
        trial.set_zero();
        trial.0[..X - offset].copy_from_slice(&r.0[offset..]);

        /*
         * q0 << j * big_digit::BITS is our actual quotient estimate - we do the shifts
         * implicitly at the end, when adding and subtracting to a and q. Not only do we
         * save the cost of the shifts, the rest of the arithmetic gets to work with
         * smaller numbers.
         */

        div_rem_assign_digit(&mut trial, n.leading_digit().unwrap());
        let mut prod = (&n * &trial).try_into().unwrap();

        // if the product of the guess with the divisor is too big, replace the guess with one less
        // According to Knuth, this loop should only run 2 times max (or even just one time with a
        // smarter check).
        while prod > Unsigned::<X>::from_slice(&r.words()[j..]) {
            trial -= &One::one();
            prod -= &n;
        }

        add_assign(&mut q.0[j..], &trial);
        // sub_assign(&mut r.0[j..], &prod.as_le_words());
        sub_assign(&mut r[j..], &prod);
    }

    debug_assert!(r < n);

    r >>= shift;
    // `a` and its shift are guaranteed to be smaller than the divisor, hence fit in `N` digits
    (q, r.try_into().unwrap())
}

impl<'a, const X: usize, const N: usize> Div<&'a Unsigned<N>> for &'a Unsigned<X> {
    type Output = Unsigned<X>;
    fn div(self, modulus: &'a Unsigned<N>) -> Self::Output {
        let (quotient, _remainder) = div_rem(self, modulus);
        quotient
    }
}

impl<'a, const X: usize, const N: usize> Div<&'a Unsigned<N>> for Unsigned<X> {
    type Output = Unsigned<X>;
    fn div(self, modulus: &'a Unsigned<N>) -> Self::Output {
        let (quotient, _remainder) = div_rem(&self, modulus);
        quotient
    }
}

impl<'a, const X: usize, const N: usize> Div<Unsigned<N>> for &'a Unsigned<X> {
    type Output = Unsigned<X>;
    fn div(self, modulus: Unsigned<N>) -> Self::Output {
        let (quotient, _remainder) = div_rem(self, &modulus);
        quotient
    }
}

impl<'a, const X: usize, const N: usize> Div<Unsigned<N>> for Unsigned<X> {
    type Output = Unsigned<X>;
    fn div(self, modulus: Unsigned<N>) -> Self::Output {
        let (quotient, _remainder) = div_rem(&self, &modulus);
        quotient
    }
}

impl<'a, const X: usize, const N: usize> Rem<&'a Unsigned<N>> for &'a Unsigned<X> {
    type Output = Unsigned<N>;
    fn rem(self, modulus: &'a Unsigned<N>) -> Self::Output {
        let (_quotient, remainder) = div_rem(self, modulus);
        remainder
    }
}

impl<'a, const X: usize, const N: usize> Rem<Unsigned<N>> for &'a Unsigned<X> {
    type Output = Unsigned<N>;
    fn rem(self, modulus: Unsigned<N>) -> Self::Output {
        let (_quotient, remainder) = div_rem(self, &modulus);
        remainder
    }
}

impl<'a, const X: usize, const N: usize> Rem<&'a Unsigned<N>> for Unsigned<X> {
    type Output = Unsigned<N>;
    fn rem(self, modulus: &'a Unsigned<N>) -> Self::Output {
        let (_quotient, remainder) = div_rem(&self, modulus);
        remainder
    }
}

impl<'a, const X: usize, const N: usize> Rem<Unsigned<N>> for Unsigned<X> {
    type Output = Unsigned<N>;
    fn rem(self, modulus: Unsigned<N>) -> Self::Output {
        let (_quotient, remainder) = div_rem(&self, &modulus);
        remainder
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

    pub const N1: u32 = -1i32 as u32;
    pub const N2: u32 = -2i32 as u32;
    pub const M: u32 = u32::MAX;

    /// Assert that an op works for all val/ref combinations
    macro_rules! assert_op {
        ($left:ident $op:tt $right:ident == $expected:expr) => {
            assert_eq!((&$left) $op (&$right), $expected);
            assert_eq!((&$left) $op $right.clone(), $expected);
            assert_eq!($left.clone() $op (&$right), $expected);
            assert_eq!($left.clone() $op $right.clone(), $expected);
        };
    }

    /// Assert that an assign-op works for all val/ref combinations
    macro_rules! assert_assign_op {
        ($left:ident $op:tt $right:ident == $expected:expr) => {{
            let mut left = $left.clone();
            assert_eq!({ left $op &$right; left}, $expected);

            let mut left = $left.clone();
            assert_eq!({ left $op $right.clone(); left}, $expected);
        }};
    }

    pub const MUL_TRIPLES: &'static [(&'static [u32], &'static [u32], &'static [u32])] = &[
        (&[], &[], &[]),
        (&[], &[1], &[]),
        (&[2], &[], &[]),
        (&[1], &[1], &[1]),
        (&[2], &[3], &[6]),
        (&[1], &[1, 1, 1], &[1, 1, 1]),
        (&[1, 2, 3], &[3], &[3, 6, 9]),
        (&[1, 1, 1], &[N1], &[N1, N1, N1]),
        (&[1, 2, 3], &[N1], &[N1, N2, N2, 2]),
        (&[1, 2, 3, 4], &[N1], &[N1, N2, N2, N2, 3]),
        (&[N1], &[N1], &[1, N2]),
        (&[N1, N1], &[N1], &[1, N1, N2]),
        (&[N1, N1, N1], &[N1], &[1, N1, N1, N2]),
        (&[N1, N1, N1, N1], &[N1], &[1, N1, N1, N1, N2]),
        (&[M / 2 + 1], &[2], &[0, 1]),
        (&[0, M / 2 + 1], &[2], &[0, 0, 1]),
        (&[1, 2], &[1, 2, 3], &[1, 4, 7, 6]),
        (&[N1, N1], &[N1, N1, N1], &[1, 0, N1, N2, N1]),
        (&[N1, N1, N1], &[N1, N1, N1, N1], &[1, 0, 0, N1, N2, N1, N1]),
        (&[0, 0, 1], &[1, 2, 3], &[0, 0, 1, 2, 3]),
        (&[0, 0, 1], &[0, 0, 0, 1], &[0, 0, 0, 0, 0, 1]),
    ];

    pub const DIV_REM_QUADRUPLES: &'static [(
        &'static [u32],
        &'static [u32],
        &'static [u32],
        &'static [u32],
    )] = &[
            (&[1], &[2], &[], &[1]),
            (&[3], &[2], &[1], &[1]),
            (&[1, 1], &[2], &[M / 2 + 1], &[1]),
            (&[1, 1, 1], &[2], &[M / 2 + 1, M / 2 + 1], &[1]),
            (&[0, 1], &[N1], &[1], &[1]),
            (&[N1, N1], &[N2], &[2, 1], &[3]),
        ];

    #[test]
    fn test_div_rem() {
        for case in MUL_TRIPLES.iter() {
            let (a_vec, b_vec, c_vec) = *case;
            let a = Unsigned::<7>::from_slice(a_vec);
            let b = Unsigned::<7>::from_slice(b_vec);
            let c = Unsigned::<7>::from_slice(c_vec);

            if !a.is_zero() {
                assert_op!(c / a == b);
                assert_op!(c % a == Unsigned::<7>::zero());
                // assert_assign_op!(c /= a == b);
                // assert_assign_op!(c %= a == Zero::zero());
                // assert_eq!(c.div_rem(&a), (b.clone(), Zero::zero()));
                assert_eq!(div_rem(&c, &a), (b.clone(), Zero::zero()));
            }
            if !b.is_zero() {
                assert_op!(c / b == a);
                assert_op!(c % b == Unsigned::<7>::zero());
                // assert_assign_op!(c /= b == a);
                // assert_assign_op!(c %= b == Zero::zero());
                // assert_eq!(c.div_rem(&b), (a.clone(), Zero::zero()));
                assert_eq!(div_rem(&c, &b), (a.clone(), Zero::zero()));
            }
        }

            for case in DIV_REM_QUADRUPLES.iter() {
                let (a_vec, b_vec, c_vec, d_vec) = *case;
                let a = Unsigned::<7>::from_slice(a_vec);
                let b = Unsigned::<7>::from_slice(b_vec);
                let c = Unsigned::<7>::from_slice(c_vec);
                let d = Unsigned::<7>::from_slice(d_vec);

            if !b.is_zero() {
                assert_op!(a / b == c);
                assert_op!(a % b == d);
        //         assert_assign_op!(a /= b == c);
        //         assert_assign_op!(a %= b == d);
                assert!(div_rem(&a, &b) == (c, d));
            }
        }
    }
}
