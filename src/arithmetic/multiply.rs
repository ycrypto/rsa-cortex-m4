use core::ops::Mul;

use crate::{AsNormalizedLittleEndianWords, Digit, DoubleDigit, Modular, Montgomery, Square, Unsigned};
use crate::numbers::{Bits, Zero};

/// This just drops (saturates?) if `lhs * rhs` does not fit in a U.
pub(crate) fn dropping_mul<U, V>(lhs: &U, rhs: &V) -> U
where
    U: AsNormalizedLittleEndianWords + Zero,
    V: AsNormalizedLittleEndianWords,
{
    let mut product: U = Zero::zero();
    let mut accumulator = DoubleDigit::default();

    for k in 0..U::CAPACITY {
        // TODO: figure out proper loop (although maybe the compiler is smart enough?)
        for i in 0..lhs.len() {
            for j in 0..rhs.len() {
                if i + j == k {
                    accumulator += (lhs[i] as u64) * (rhs[j] as u64);
                }
            }
        }
        product[k] = accumulator as Digit;
        accumulator = accumulator >> Digit::BITS;
    }
    product
}

impl <'l, const L: usize> Mul for &'l Unsigned<L> {

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

/// Currently see no way of ensuring that both factors have the same modulus
/// on a type level; hence a runtime debug_assert instead.
impl<'l, 'n, const L: usize> Mul for &'l Modular<'n, L> {
    type Output = Modular<'n, L>;

    fn mul(self, other: Self) -> Self::Output {
        debug_assert!(self.n == other.n);
        let n: &Unsigned<L> = self.n;

        let product = &self.x * &other.x;
        let reduced = product % n;
        Modular { x: reduced, n: self.n }
    }
}
// /// Computes z mod m = x * y * 2 ** (-n*_W) mod m
// /// assuming k = -1/m mod 2**_W
// /// See Gueron, "Efficient Software Implementations of Modular Exponentiation".
// /// https://eprint.iacr.org/2011/239.pdf
// /// In the terminology of that paper, this is an "Almost Montgomery Multiplication":
// /// x and y are required to satisfy 0 <= z < 2**(n*_W) and then the result
// /// z is guaranteed to satisfy 0 <= z < 2**(n*_W), but it may not be < m.
// fn montgomery(z: &mut BigUint, x: &BigUint, y: &BigUint, m: &BigUint, k: BigDigit, n: usize) {

impl<'l, 'n, const L: usize> Mul for &'l Montgomery<'n, L> {
    type Output = Montgomery<'n, L>;

    fn mul(self, other: Self) -> Self::Output {
        todo!();
    }
}
