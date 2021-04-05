use core::{cmp::Ordering, ops::{Div, Rem}};

use crate::{Array, Digit, DoubleDigit, FromSlice, Number, NumberMut, Unsigned};
use crate::numbers::{Bits, One, Zero};

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
pub fn div_rem_assign_digit(x: &mut impl NumberMut, n: Digit) -> Digit {
    let mut remainder = 0;

    // run down the digits in x, dividing each by n, while carrying along the remainder
    let l = x.len();
    for digit in x[..l].iter_mut().rev() {
        let (q, r) = div_digits(remainder, *digit, n);
        *digit = q;
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

//// pub fn div_rem<const M: usize, const N: usize>(x: &Unsigned<M + N>, n: &Unsigned<N>) -> (Unsigned<M + 1>, Unsigned<N>) {
//// pub fn div_rem<const M: usize, const N: usize>(x: &Product<M, N>, n: &Unsigned<N>) -> (UnsignedCarry<M>, Unsigned<N>) {
//pub fn div_rem<const X: usize, const N: usize>(x: &Unsigned<X>, n: &Unsigned<N>) -> (Unsigned<X>, Unsigned<N>) {
//    if n.is_zero() {
//        todo!("specialize to `mod 2**{{32*N}}, maybe");
//    }
//    if x.is_zero() {
//        return (Default::default(), Default::default());
//    }

//    if n.len() == 1 {
//        let n = n[0];

//        let mut div = x.clone();
//        if n == 1 {
//            return (div, Zero::zero());
//        } else {
//            let rem = div_rem_assign_digit(&mut div, n);
//            return (div, rem.into());
//        }
//    }

//    // let n = n.as_le_words();

//    // Required or the q_len calculation below can underflow:
//    // match x.as_le_words().cmp(&n.as_le_words()) {
//    match x.partial_cmp(n).unwrap() {
//        Ordering::Less => return (Zero::zero(), n.clone()),
//        Ordering::Equal => return (One::one(), Zero::zero()),
//        Ordering::Greater => {} // Do nothing
//    }

//    // This algorithm is from Knuth, TAOCP vol 2 section 4.3, algorithm D:
//    //
//    // Shift n to set highest bit (in its leading digit), so the generated guesses are as
//    // large as possible in the following loop.
//    //
//    // This shift has no influence on `q`, and will be reverted for `r` at the end.
//    // let shift = n.as_le_words().last().unwrap().leading_zeros() as usize;
//    let shift = n.leading_digit().unwrap().leading_zeros() as usize;

//    let mut r = x << shift;
//    // by the above, x >= n, so `n` and its shift `b` must fit into Unsigned::<X>, as `x` does
//    // let b: Unsigned<X> = (n << shift).try_into().unwrap();
//    let n: Unsigned<X> = (n << shift).into_unsigned();

//    // we now want to calculate a/b, in the sense a = qb + r
//    // in this sense, a = r (starts at a, goes down to r by removing multiples of b, the
//    // multipliers summed into q, which starts at 0)

//    // The algorithm works by incrementally calculating "guesses", q0, for part of the
//    // remainder. Once we have any number q0 such that q0 * b <= a, we can set
//    //
//    //     q += q0
//    //     a -= q0 * b
//    //
//    // and then iterate until a < b. Then, (q, a) will be our desired quotient and remainder.
//    //
//    // q0, our guess, is calculated by dividing the last few digits of a by the last digit of b
//    // - this should give us a guess that is "close" to the actual quotient, but is possibly
//    // greater than the actual quotient. If q0 * b > a, we simply use iterated subtraction
//    // until we have a guess such that q0 * b <= a.

//    let q_len = x.len() - n.len() + 1;
//    let mut q = Unsigned::<X>::default();

//    // We reuse the same temporary to avoid hitting the allocator in our inner loop - this is
//    // sized to hold a0 (in the common case; if a particular digit of the quotient is zero a0
//    // can be bigger).
//    //

//    // // this is the "trial division" that Montgomery would later refer to :)
//    // let mut trial = Unsigned::<X>::default(); // SmallVec::with_capacity(2)

//    for j in (0..q_len).rev() {
//        /*
//         * When calculating our next guess q0, we don't need to consider the digits below j
//         * + b.len() - 1: we're guessing digit j of the quotient (i.e. q0 << j) from
//         * digit bn of the divisor (i.e. bn << (b.data.len() - 1) - so the product of those
//         * two numbers will be zero in all digits up to (j + b.data.len() - 1).
//         */
//        let offset = j + n.len() - 1;
//        if offset >= r.len() {
//            continue;
//        }

//        // set "trial" to current remainder, immediately after we divide by highest digit of
//        // divisor `n` to get a guess.
//        // trial.set_zero();
//        // trial[..r.len() - offset].copy_from_slice(&r[offset..]);
//        let mut trial = Unsigned::<X>::from_slice(&r[offset..]);

//        /*
//         * q0 << j * big_digit::BITS is our actual quotient estimate - we do the shifts
//         * implicitly at the end, when adding and subtracting to a and q. Not only do we
//         * save the cost of the shifts, the rest of the arithmetic gets to work with
//         * smaller numbers.
//         */

//        div_rem_assign_digit(&mut trial, n.leading_digit().unwrap());
//        let mut prod: Unsigned<X> = (&n * &trial).into_unsigned();

//        // if the product of the guess with the divisor is too big, replace the guess with one less
//        // According to Knuth, this loop should only run 2 times max (or even just one time with a
//        // smarter check).
//        while prod > Unsigned::<X>::from_slice(&r[j..]) {
//            trial -= &Unsigned::<X>::one();
//            prod -= &n;
//        }

//        // Unfortunately, don't see a way to use operators here (wrapped types don't work,
//        // and slices are foreign types).
//        super::add::add_assign(&mut q[j..], &trial);
//        super::subtract::sub_assign(&mut r[j..], &prod);
//    }

//    debug_assert!(n > r);
//    debug_assert!(r < n);

//    r >>= shift;
//    // `a` and its shift are guaranteed to be smaller than the divisor, hence fit in `N` digits
//    (q, r.into_unsigned())
//}

// N,M in "reversed" order in Product to cover UnsignedCarry case (M = 1).
//
// TODO: See if we can't set `x: &T` where `T: AsNormalizedLittleEndianWords`, and just
// debug_assert that T::CAPACITY > N.
pub fn generic_div_rem<T, const D: usize, const E: usize>(x: &T, n: &Unsigned<D, E>) -> (T, Unsigned<D, E>)
where
    T: Number + Clone + One + Zero + FromSlice + PartialOrd + core::ops::ShrAssign<usize>,
    T: core::ops::ShrAssign<usize>,
    for<'a> &'a T: core::ops::Shl<usize, Output = T>,
    for<'a> T: core::ops::SubAssign<&'a Unsigned<D, E>>,
    for<'a> T: core::ops::SubAssign<&'a T>,
{

    if x.is_zero() {
        return (Zero::zero(), Zero::zero());
    }

    if n.len() == 1 {
        let n = n[0];

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
    match n.partial_cmp(x).unwrap() {
        Ordering::Greater => return (Zero::zero(), n.clone()),
        Ordering::Equal => return (One::one(), Zero::zero()),
        Ordering::Less => {} // Do nothing
    }

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

    let q_len = x.len() - n.len() + 1;
    let mut q: T = Zero::zero();

    let mut trial: T = Zero::zero();

    for j in (0..q_len).rev() {
        let offset = j + n.len() - 1;
        if offset >= r.len() {
            continue;
        }

        trial.set_zero();
        trial[..r.len() - offset].copy_from_slice(&r[offset..]);

        div_rem_assign_digit(&mut trial, n.leading_digit().unwrap());
        let mut prod = super::multiply::dropping_mul(&trial, &n);

        while prod > T::from_slice(&r[j..]) {
            trial -= &T::one();
            prod -= &n;
        }

        // Unfortunately, don't see a way to use operators here (wrapped types don't work,
        // and slices are foreign types).
        super::add::add_assign(&mut q[j..], &trial);
        super::subtract::sub_assign(&mut r[j..], &prod);
    }

    debug_assert!(n > r);

    r >>= shift_bits;
    // `a` and its shift are guaranteed to be smaller than the divisor, hence fit in `N` digits
    (q, r.into_unsigned())
}



//
// Implement Div
//

impl<'a, const D: usize, const E: usize, const F: usize, const G: usize> Div<&'a Unsigned<F, G>> for &'a Unsigned<D, E> {
    type Output = Unsigned<D, E>;
    fn div(self, modulus: &'a Unsigned<F, G>) -> Self::Output {
        let (quotient, _remainder) = generic_div_rem(self, modulus);
        quotient
    }
}

// the following three derived implementations are currently only
// used for the assert_op tests
impl<'a, const D: usize, const E: usize, const F: usize, const G: usize> Div<&'a Unsigned<F, G>> for Unsigned<D, E> {
    type Output = Unsigned<D, E>;
    fn div(self, modulus: &'a Unsigned<F, G>) -> Self::Output {
        let (quotient, _remainder) = generic_div_rem(&self, modulus);
        quotient
    }
}

impl<'a, const D: usize, const E: usize, const F: usize, const G: usize> Div<Unsigned<F, G>> for &'a Unsigned<D, E> {
    type Output = Unsigned<D, E>;
    fn div(self, modulus: Unsigned<F, G>) -> Self::Output {
        let (quotient, _remainder) = generic_div_rem(self, &modulus);
        quotient
    }
}

impl<const D: usize, const E: usize, const F: usize, const G: usize> Div<Unsigned<F, G>> for Unsigned<D, E> {
    type Output = Unsigned<D, E>;
    fn div(self, modulus: Unsigned<F, G>) -> Self::Output {
        let (quotient, _remainder) = generic_div_rem(&self, &modulus);
        quotient
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
        let (_quotient, remainder) = generic_div_rem(&self, modulus);
        remainder
    }
}

impl<'a, const D: usize, const E: usize, const F: usize, const G: usize> Rem<Unsigned<F, G>> for &'a Unsigned<D, E> {
    type Output = Unsigned<F, G>;
    fn rem(self, modulus: Unsigned<F, G>) -> Self::Output {
        let (_quotient, remainder) = generic_div_rem(self, &modulus);
        remainder
    }
}

impl<'a, const D: usize, const E: usize, const F: usize, const G: usize> Rem<Unsigned<F, G>> for Unsigned<D, E> {
    type Output = Unsigned<F, G>;
    fn rem(self, modulus: Unsigned<F, G>) -> Self::Output {
        let (_quotient, remainder) = generic_div_rem(&self, &modulus);
        remainder
    }
}



impl<'a, const D: usize, const E: usize, const F: usize, const G: usize, const L: usize> Rem<&'a Unsigned<F, G>> for &'a Array<D, E, L> {
    type Output = Unsigned<F, G>;
    fn rem(self, modulus: &'a Unsigned<F, G>) -> Self::Output {
        let (_quotient, remainder) = generic_div_rem(self, modulus);
        remainder
    }
}

// impl<'a, const X: usize, const N: usize> Rem<Unsigned<N>> for &'a Unsigned<X> {
//     type Output = Unsigned<N>;
//     fn rem(self, modulus: Unsigned<N>) -> Self::Output {
//         let (_quotient, remainder) = generic_div_rem(self, &modulus);
//         remainder
//     }
// }

// impl<'a, const X: usize, const N: usize> Rem<&'a Unsigned<N>> for Unsigned<X> {
//     type Output = Unsigned<N>;
//     fn rem(self, modulus: &'a Unsigned<N>) -> Self::Output {
//         let (_quotient, remainder) = generic_div_rem(&self, modulus);
//         remainder
//     }
// }

// impl<'a, const X: usize, const N: usize> Rem<Unsigned<N>> for Unsigned<X> {
//     type Output = Unsigned<N>;
//     fn rem(self, modulus: Unsigned<N>) -> Self::Output {
//         let (_quotient, remainder) = generic_div_rem(&self, &modulus);
//         remainder
//     }
// }

// impl<const L: usize, const M: usize, const N: usize> Rem<&Unsigned<L>> for Product<M, N> {
//     type Output = Unsigned<L>;
//     fn rem(self, modulus: &Self::Output) -> Self::Output {
//         let (_quotient, remainder) = generic_div_rem(&self, &modulus);
//         remainder
//     }
// }

#[cfg(test)]
mod test {
    use super::*;

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

    // /// Assert that an assign-op works for all val/ref combinations
    // macro_rules! assert_assign_op {
    //     ($left:ident $op:tt $right:ident == $expected:expr) => {{
    //         let mut left = $left.clone();
    //         assert_eq!({ left $op &$right; left}, $expected);

    //         let mut left = $left.clone();
    //         assert_eq!({ left $op $right.clone(); left}, $expected);
    //     }};
    // }

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
                assert_eq!(generic_div_rem(&c, &a), (b.clone(), Zero::zero()));
            }
            if !b.is_zero() {
                assert_op!(c / b == a);
                assert_op!(c % b == Short::<7>::zero());
                // assert_assign_op!(c /= b == a);
                // assert_assign_op!(c %= b == Zero::zero());
                // assert_eq!(c.div_rem(&b), (a.clone(), Zero::zero()));
                assert_eq!(generic_div_rem(&c, &b), (a.clone(), Zero::zero()));
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
}
