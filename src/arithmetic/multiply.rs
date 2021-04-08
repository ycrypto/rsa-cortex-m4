use core::ops::Mul;

use crate::{Digit, DoubleDigit, Modular, Montgomery, Unsigned};
use crate::numbers::{Bits, Number, NumberMut, Product, Zero};

/// This just drops (saturates?) if `lhs * rhs` does not fit in a U.
pub(crate) fn dropping_mul<U, V>(lhs: &U, rhs: &V) -> U
where
    U: NumberMut + Zero + core::fmt::Debug,
    V: Number + core::fmt::Debug,
{
    let mut product: U = Zero::zero();

    // #[cfg(test)]
    // println!("BITS = {:?}", Digit::BITS);
    // #[cfg(test)]
    // println!("U = {:?}", lhs);
    // #[cfg(test)]
    // println!("V = {:?}", rhs);

    for j in 0..core::cmp::min(U::CAPACITY, rhs.len()) {
        let yj = rhs[j] as DoubleDigit;
        let mut accumulator = 0;
        for i in 0..(U::CAPACITY - j) {
            let xi = lhs.padded_number()[i] as DoubleDigit;
            accumulator += (product.padded_number()[i + j] as DoubleDigit) + xi*yj;
            product[i + j] = accumulator as Digit;
            accumulator >>= Digit::BITS;
        }
    }

    product
}

impl <const D: usize, const E: usize> Mul for &Unsigned<D, E> {

    type Output = Product<D, E>;

    /// product-scanning implementation of multiplication
    fn mul(self, other: Self) -> Self::Output {
        let mut product = Product::default();
        let mut accumulator = DoubleDigit::default();

        for k in 0..2*(D + E) {
            // TODO: figure out proper loop (although maybe the compiler is smart enough?)
            for i in 0..self.len() {
                for j in 0..other.len() {
                    if i + j == k {
                        accumulator += (self[i] as DoubleDigit) * (other[j] as DoubleDigit);
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
impl<'l, 'n, const D: usize, const E: usize> Mul for &'l Modular<'n, D, E> {
    type Output = Modular<'n, D, E>;

    fn mul(self, other: Self) -> Self::Output {
        debug_assert_eq!(**self.n, **other.n);
        let n: &Unsigned<D, E> = self.n;

        let product = &self.x * &other.x;
        let reduced = &product % &*n;
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

impl<'n, const D: usize, const E: usize> Mul for &Montgomery<'n, D, E> {
    type Output = Montgomery<'n, D, E>;

    fn mul(self, _other: Self) -> Self::Output {
        todo!();
    }
}
