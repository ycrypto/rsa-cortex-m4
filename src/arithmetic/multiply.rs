use core::ops::Mul;

use crate::{Digit, DoubleDigit, Square, Unsigned};
use crate::numbers::Bits;

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


