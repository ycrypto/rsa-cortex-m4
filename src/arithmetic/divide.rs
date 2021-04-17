use core::{cmp::Ordering, convert::TryInto, ops::{Div, Rem}};

use ref_cast::RefCast;

use crate::{Digit, DoubleDigit, Odd, Result, Unsigned, Wrapping};
use crate::numbers::{Array, Bits, Number, NumberMut};

/// Odd numbers can be inverted modulo $2^m$
pub fn wrapping_invert_odd<const D: usize, const E: usize>(x: &Odd<D, E>) -> Odd<D, E> {
    #[allow(non_snake_case)]
    let T = (D + E) * (Digit::BITS.trailing_zeros() as usize);

    let x: &Unsigned<D, E> = &*x;
    let mut y = Unsigned::from(1);
    let two: Unsigned<D, E> = Unsigned::from(2);

    for _ in 1..=T {
        // y = &y * &(&two - &(x * &y));
        y = y.wrapping_mul(&(two.wrapping_sub(&x.wrapping_mul(&y))));
    }
    Odd(y)
}

pub fn wrapping_invert<const D: usize, const E: usize>(unsigned: &Unsigned<D, E>) -> Result<Unsigned<D, E>> {
    let odd: &Odd<D, E> = unsigned.try_into()?;
    Ok(wrapping_invert_odd(odd).into())
}
// /// Input:  x = (x_0,x_1,...,x_n), n = (n_0,n_1, ...n_t, 0, ...0), 1 <= t <= L, yt != 0
// /// Output: q = (q_0,q_1,...,q_{n-t}), r = (r_0,r_1,...r_t) with x=qy+r, 0<=r<y
// fn div_rem<const L: usize>(x: &mut Unsigned<L>, n: &Odd<L>) -> (Unsigned<L>, Unsigned<L>) {
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
pub fn div_digits(hi: Digit, lo: Digit, divisor: Digit) -> (Digit, Digit) {
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
pub fn div_rem_assign_digit<N: NumberMut>(number: &mut N, modulus: Digit) -> Digit {
    let mut remainder = 0;

    // run down the digits in x, dividing each by n, while carrying along the remainder
    #[cfg(not(feature = "ct-maybe"))]
    let l = number.significant_digits().len();

    #[cfg(feature = "ct-maybe")]
    let l = N::DIGITS;

    for digit in number[..l].iter_mut().rev() {
        let (quotient, r) = div_digits(remainder, *digit, modulus);
        *digit = quotient;
        remainder = r;
    }

    remainder
}

///// "Multi-precision division of x by n".
/////
///// Meaning: Return unique values `(q, r)` with `x = q*n + r`, and `0 <= r < n`.
/////
///// To do this in the general case means making quite a few guesses -> this operation is to be used
///// sparingly; there are many tricks available in the literature to avoid it.
/////
///// Currently, this copies the implementation in [`num-bigint::biguint::division`][num-bigint].
/////
///// [num-bigint]: https://docs.rs/num-bigint/0.4.0/src/num_bigint/biguint/division.rs.html#111-156

//// this should really be: (m + n) / n --> ((m + 1), n) in terms of "places", to use Knuth's language
//// pub fn div_rem<const M: usize, const N: usize>(x: &Square<M, N>, n: &Unsigned<N>) -> (UnsignedCarry<M>, Unsigned<N>) {
////
//// But, the `n` argument does not need to have N places, just because it fits into N words.

// N,M in "reversed" order in Product to cover UnsignedCarry case (M = 1).
//
// TODO: See if we can't set `x: &T` where `T: AsNormalizedLittleEndianWords`, and just
// debug_assert that T::DIGITS > N.
pub fn generic_div_rem<T, const D: usize, const E: usize>(x: &T, n: &Unsigned<D, E>) -> (T, Unsigned<D, E>)
where
    T: NumberMut + PartialOrd,
    T: core::ops::ShrAssign<usize>,
    for<'a> &'a T: core::ops::Shl<usize, Output = T>,
    for<'a> Wrapping<T>: core::ops::SubAssign<&'a Unsigned<D, E>>,
    for<'a> Wrapping<T>: core::ops::SubAssign<&'a T>,
{

    if x.is_zero() {
        return (T::zero(), Unsigned::zero())
    }

    if n.is_digit() {
        let n = n[0];

        let mut div = x.clone();
        if n == 1 {
            return (div, Unsigned::zero());
        } else {
            let rem = div_rem_assign_digit(&mut div, n);
            return (div, rem.into());
        }
    }

    // Required or the q_len calculation below can underflow:
    // match x.as_le_words().cmp(&n.as_le_words()) {
    match n.partial_cmp(x).unwrap() {
        Ordering::Greater => return (T::zero(), Unsigned::from_slice(&x)),
        Ordering::Equal => return (T::one(), Unsigned::zero()),
        Ordering::Less => {} // Do nothing
    }


    // // 2021-04-06: workaround
    // let n =  Unsigned<

    // Knuth, TAOCP vol 2 section 4.3, algorithm D(ivision)
    //
    // This shift has no influence on `q`, and will be reverted for `r` at the end.
    // let shift = n.as_le_words().last().unwrap().leading_zeros() as usize;
    let shift_bits = n.leading_digit().unwrap().leading_zeros() as usize;

    let mut r: T = x << shift_bits;
    // by the above, x >= n, so `n` and its shift `b` must fit into Unsigned::<X>, as `x` does
    // let b: Unsigned<X> = (n << shift).try_into().unwrap();
    let n: Unsigned<D, E> = n << shift_bits;

    // we now want to calculate a/b, in the sense a = qb + r
    // in this sense, a = r (starts at a, goes down to r by removing multiples of b, the
    // multipliers summed into q, which starts at 0)

    let q_len = x.significant_digits().len() - n.significant_digits().len() + 1;
    let mut q = T::zero();

    let mut trial = T::zero();

    for j in (0..q_len).rev() {
        let offset = j + n.significant_digits().len() - 1;
        let r_len = r.significant_digits().len();
        if offset >= r.significant_digits().len() {
            continue;
        }

        trial.set_zero();
        trial[..r_len - offset].copy_from_slice(&r[offset..r_len]);

        div_rem_assign_digit(&mut trial, n.leading_digit().unwrap());
        let mut prod = super::multiply::wrapping_mul(&trial, &n);

        while prod > T::from_slice(&r[j..]) {
            *Wrapping::ref_cast_mut(&mut trial) -= &T::one();
            *Wrapping::ref_cast_mut(&mut prod) -= &n;
        }

        // Unfortunately, don't see a way to use operators here (wrapped types don't work,
        // and slices are foreign types).
        super::add::wrapping_add_assign(&mut q[j..], trial.significant_digits());
        super::subtract::sub_assign_borrow(&mut r[j..], prod.significant_digits());
    }

    debug_assert!(n > r);

    r >>= shift_bits;
    // `a` and its shift are guaranteed to be smaller than the divisor, hence fit in `N` digits
    // assert!(!r.to_unsigned::<D, E>().unwrap().is_zero());
    (q, r.to_unsigned().unwrap())
}

// Inversion

impl<const D: usize, const E: usize> Wrapping<Unsigned<D, E>> {
    /// See `Unsigned::wrapping_inv`.
    pub fn inv(&self) -> Result<Self> {
        wrapping_invert(&self.0).map(Wrapping)
    }
}

impl<const D: usize, const E: usize> Unsigned<D, E> {
    /// The wrapping inverse, i.e., the exact inverse w.r.t wrapping multiplication.
    ///
    /// Exists if and only if the number is odd.
    ///
    /// This uses $\mathcal{O}(\log n)$ loops in `Self::BITS`, very efficient (!)
    ///
    /// Source: Fig. 1 from
    /// [GCD-Free Algorithms for Computing Modular Inverses (2003)][joy-paillier]
    ///
    /// Note that this source is highly confusing! What they mean to say
    /// is to iterate $y \leftarrow y(2 - ey)$ in $\mathbb{Z}/2^{|f|}$,
    /// where the output is an inverse of $e$ modulo $2^{2i}$.
    /// In other words, the $\text{mod }2^i$ is a typo, and should be $\text{mod }2^{|f|}$.
    ///
    /// cf. also [Crypto StackExchange][cse].
    ///
    /// [joy-paillier]: https://api.semanticscholar.org/CorpusID:17736455
    /// [cse]: https://crypto.stackexchange.com/a/47496
    pub fn wrapping_inv(&self) -> Result<Self> {
        wrapping_invert(&self)
    }
}

//
// Implement Div
//

impl<'a, const D: usize, const E: usize, const F: usize, const G: usize> Div<&'a Unsigned<F, G>> for &'a Unsigned<D, E> {
    type Output = Unsigned<D, E>;
    fn div(self, modulus: &'a Unsigned<F, G>) -> Self::Output {
        generic_div_rem(self, modulus).0
    }
}

// the following three derived implementations are currently only
// used for the assert_op tests
impl<'a, const D: usize, const E: usize, const F: usize, const G: usize> Div<&'a Unsigned<F, G>> for Unsigned<D, E> {
    type Output = Unsigned<D, E>;
    fn div(self, modulus: &'a Unsigned<F, G>) -> Self::Output {
        generic_div_rem(&self, modulus).0
    }
}

impl<'a, const D: usize, const E: usize, const F: usize, const G: usize> Div<Unsigned<F, G>> for &'a Unsigned<D, E> {
    type Output = Unsigned<D, E>;
    fn div(self, modulus: Unsigned<F, G>) -> Self::Output {
        generic_div_rem(self, &modulus).0
    }
}

impl<const D: usize, const E: usize, const F: usize, const G: usize> Div<Unsigned<F, G>> for Unsigned<D, E> {
    type Output = Unsigned<D, E>;
    fn div(self, modulus: Unsigned<F, G>) -> Self::Output {
        generic_div_rem(&self, &modulus).0
    }
}



//
// Implement Rem
//

impl<'a, const D: usize, const E: usize, const F: usize, const G: usize> Rem<&'a Unsigned<F, G>> for &'a Unsigned<D, E> {
    type Output = Unsigned<F, G>;
    fn rem(self, modulus: &'a Unsigned<F, G>) -> Self::Output {
        let (_quotient, remainder) = generic_div_rem(self, modulus);
        remainder
    }
}

// the following three derived implementations are currently only
// used for the assert_op tests
impl<'a, const D: usize, const E: usize, const F: usize, const G: usize> Rem<&'a Unsigned<F, G>> for Unsigned<D, E> {
    type Output = Unsigned<F, G>;
    fn rem(self, modulus: &'a Unsigned<F, G>) -> Self::Output {
        generic_div_rem(&self, modulus).1
    }
}

impl<'a, const D: usize, const E: usize, const F: usize, const G: usize> Rem<Unsigned<F, G>> for &'a Unsigned<D, E> {
    type Output = Unsigned<F, G>;
    fn rem(self, modulus: Unsigned<F, G>) -> Self::Output {
        generic_div_rem(self, &modulus).1
    }
}

impl<'a, const D: usize, const E: usize, const F: usize, const G: usize> Rem<Unsigned<F, G>> for Unsigned<D, E> {
    type Output = Unsigned<F, G>;
    fn rem(self, modulus: Unsigned<F, G>) -> Self::Output {
        generic_div_rem(&self, &modulus).1
    }
}



impl<'a, const D: usize, const E: usize, const F: usize, const G: usize, const L: usize> Rem<&'a Unsigned<F, G>> for &'a Array<D, E, L> {
    type Output = Unsigned<F, G>;
    fn rem(self, modulus: &'a Unsigned<F, G>) -> Self::Output {
        generic_div_rem(self, modulus).1
    }
}

#[cfg(test)]
mod test {
    use super::*;

    pub const N1: Digit = -1i64 as Digit;
    pub const N2: Digit = -2i64 as Digit;
    pub const M: Digit = Digit::MAX;

    /// Assert that an op works for all val/ref combinations
    macro_rules! assert_op {
        ($left:ident $op:tt $right:ident == $expected:expr) => {
            assert_eq!((&$left) $op (&$right), $expected);
            assert_eq!((&$left) $op $right.clone(), $expected);
            assert_eq!($left.clone() $op (&$right), $expected);
            assert_eq!($left.clone() $op $right.clone(), $expected);
        };
    }

    // /// Assert that an assign-op works for all val/ref combinations
    // macro_rules! assert_assign_op {
    //     ($left:ident $op:tt $right:ident == $expected:expr) => {{
    //         let mut left = $left.clone();
    //         assert_eq!({ left $op &$right; left}, $expected);

    //         let mut left = $left.clone();
    //         assert_eq!({ left $op $right.clone(); left}, $expected);
    //     }};
    // }

    pub const MUL_TRIPLES: &'static [(&'static [Digit], &'static [Digit], &'static [Digit])] = &[
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
        &'static [Digit],
        &'static [Digit],
        &'static [Digit],
        &'static [Digit],
    )] = &[
            (&[1], &[2], &[], &[1]),
            (&[3], &[2], &[1], &[1]),
            (&[1, 1], &[2], &[M / 2 + 1], &[1]),
            (&[1, 1, 1], &[2], &[M / 2 + 1, M / 2 + 1], &[1]),
            (&[0, 1], &[N1], &[1], &[1]),
            (&[N1, N1], &[N2], &[2, 1], &[3]),
        ];

    #[test]
    fn rem_of_1() {
        use crate::fixtures::*;
        let short1 = Short256::from(1);
        let p = p256().into_unsigned();

        let remainder = &short1 % &p;

        assert_eq!(remainder, short1);
    }

    #[test]
    fn test_div_rem() {
        use crate::Short;
        for case in MUL_TRIPLES.iter() {
            let (a_vec, b_vec, c_vec) = *case;
            let a = Short::<7>::from_slice(a_vec);
            let b = Short::<7>::from_slice(b_vec);
            let c = Short::<7>::from_slice(c_vec);

            if !a.is_zero() {
                assert_op!(c / a == b);
                assert_op!(c % a == Short::<7>::zero());
                // assert_assign_op!(c /= a == b);
                // assert_assign_op!(c %= a == Zero::zero());
                // assert_eq!(c.div_rem(&a), (b.clone(), Zero::zero()));
                assert_eq!(generic_div_rem(&c, &a), (b.clone(), Unsigned::zero()));
            }
            if !b.is_zero() {
                assert_op!(c / b == a);
                assert_op!(c % b == Short::<7>::zero());
                // assert_assign_op!(c /= b == a);
                // assert_assign_op!(c %= b == Zero::zero());
                // assert_eq!(c.div_rem(&b), (a.clone(), Zero::zero()));
                assert_eq!(generic_div_rem(&c, &b), (a.clone(), Unsigned::zero()));
            }
        }

        for case in DIV_REM_QUADRUPLES.iter() {
            let (a_vec, b_vec, c_vec, d_vec) = *case;
            let a = Short::<7>::from_slice(a_vec);
            let b = Short::<7>::from_slice(b_vec);
            let c = Short::<7>::from_slice(c_vec);
            let d = Short::<7>::from_slice(d_vec);

        if !b.is_zero() {
            assert_op!(a / b == c);
            assert_op!(a % b == d);
    //         assert_assign_op!(a /= b == c);
    //         assert_assign_op!(a %= b == d);
            assert!(generic_div_rem(&a, &b) == (c, d));
            }
        }
    }

    #[test]
    fn test_invert() {
        use hex_literal::hex;
        use crate::{fixtures::Long256, Long};

        let x = Long256::from_bytes(&hex!(
            "756a33dea26163dfae8303747b3db15dc071fc5a0d75de209881a570678b33bb"));

        // unwrap does not fail since x is odd.
        let maybe_inverse = wrapping_invert(&x).unwrap();
        let maybe_one = crate::arithmetic::multiply::wrapping_mul(&maybe_inverse, &x);

        assert_eq!(maybe_one, Long::<2>::one());

        // even numbers not invertible
        let x = Long::<2>::from_slice(&[0x2, 0x1]);
        assert!(wrapping_invert(&x).is_err());

    }
}
