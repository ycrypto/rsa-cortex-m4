use core::ops::{Shl, ShlAssign, Shr, ShrAssign};

use crate::{Digit, Unsigned};
use crate::numbers::{Bits, Zero};

impl<const L: usize> ShlAssign<usize> for Unsigned<L> {
    #[inline]
    /// Compared to `num-bigint{,-dig}`, this is a truncating shift.
    ///
    /// Note that "left" means "higher number".
    ///
    /// We could consider implementing this with Output UnsignedCarry or Square,
    /// if necessary.
    fn shl_assign(&mut self, bits: usize) {
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

impl<const L: usize> ShrAssign<usize> for Unsigned<L> {

    #[inline]
    /// Note that "right" means "lower number".
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

impl<const L: usize> Shr<usize> for &Unsigned<L> {
    type Output = Unsigned<L>;

    #[inline]
    fn shr(self, bits: usize) -> Self::Output {
        let mut result = self.clone();
        result >>= bits;
        result
    }
}
