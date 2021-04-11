use core::ops::{Shl, ShlAssign, Shr, ShrAssign};

use crate::{Digit, Unsigned};
use crate::numbers::{Array, Bits, NumberMut};

/// Compared to `num-bigint{,-dig}`, this is a truncating shift.
///
/// Note that "left" means "higher number".
fn wrapping_shl_assign<T>(number: &mut T, bits: usize)
where
    T: NumberMut
{
    // make this CT also?
    let l = number.significant_digits().len();
    let n_digits = bits / Digit::BITS;

    // shift back by n_digits
    number.copy_within(..(l - n_digits), n_digits);
    number[..n_digits].fill(0);

    // shift back sub-digit amount of bits
    let n_bits = bits % Digit::BITS;
    if n_bits > 0 {
        let mut carry = 0;
        for elem in number[n_digits..l + n_digits + 1].iter_mut() {
            let new_carry = *elem >> (Digit::BITS - n_bits);
            *elem = (*elem << n_bits) | carry;
            carry = new_carry;
        }
    }
}
// impl<const L: usize> ShlAssign<usize> for Unsigned<L> {
//     #[inline]
//     fn shl_assign(&mut self, bits: usize) {
//         wrapping_shl_assign(self, bits)
//     }
// }

impl<const D: usize, const E: usize> ShlAssign<usize> for Unsigned<D, E> {
    #[inline]
    fn shl_assign(&mut self, bits: usize) {
        wrapping_shl_assign(self, bits)
    }
}

impl<const D: usize, const E: usize, const L: usize> ShlAssign<usize> for Array<D, E, L> {
    #[inline]
    fn shl_assign(&mut self, bits: usize) {
        wrapping_shl_assign(self, bits)
    }
}

/// Note that "right" means "lower number".
fn generic_shr_assign<T>(number: &mut T, bits: usize)
where
    T: NumberMut
{
    let l = number.significant_digits().len();
    let n_digits = bits / Digit::BITS;

    if n_digits >= l {
        number.set_zero();
        return;
    }

    // shift by n_digits
    number.copy_within(n_digits.., 0);
    // number.copy_within(n_digits.., n_digits);
    number[(l - n_digits)..l].fill(0);

    let n_bits = bits % Digit::BITS;

    if n_bits > 0 {
        let mut borrow = 0;
        for elem in number.iter_mut().rev().skip(n_digits) {
            let new_borrow = *elem << (Digit::BITS - n_bits);
            *elem = (*elem >> n_bits) | borrow;
            borrow = new_borrow;
        }
    }
}

// impl<const L: usize> ShrAssign<usize> for Unsigned<L> {

//     #[inline]
//     fn shr_assign(&mut self, bits: usize) {
//         generic_shr_assign(self, bits)
//     }
// }

impl<const D: usize, const E: usize> ShrAssign<usize> for Unsigned<D, E> {
    #[inline]
    fn shr_assign(&mut self, bits: usize) {
        generic_shr_assign(self, bits)
    }
}

impl<const D: usize, const E: usize, const L: usize> ShrAssign<usize> for Array<D, E, L> {
    #[inline]
    fn shr_assign(&mut self, bits: usize) {
        generic_shr_assign(self, bits)
    }
}


// impl<const L: usize> Shl<usize> for &Unsigned<L> {
//     type Output = Unsigned<L>;

//     #[inline]
//     fn shl(self, bits: usize) -> Self::Output {
//         let mut result = self.clone();
//         result <<= bits;
//         result
//     }
// }

impl<const D: usize, const E: usize> Shl<usize> for &Unsigned<D, E> {
    type Output = Unsigned<D, E>;

    #[inline]
    fn shl(self, bits: usize) -> Self::Output {
        let mut result = self.clone();
        result <<= bits;
        result
    }
}

impl<const D: usize, const E: usize, const L: usize> Shl<usize> for &Array<D, E, L> {
    type Output = Array<D, E, L>;

    #[inline]
    fn shl(self, bits: usize) -> Self::Output {
        let mut result = self.clone();
        result <<= bits;
        result
    }
}

// impl<const L: usize> Shr<usize> for &Unsigned<L> {
//     type Output = Unsigned<L>;

//     #[inline]
//     fn shr(self, bits: usize) -> Self::Output {
//         let mut result = self.clone();
//         result >>= bits;
//         result
//     }
// }

impl<const D: usize, const E: usize, const L: usize> Shr<usize> for &Array<D, E, L> {
    type Output = Array<D, E, L>;

    #[inline]
    fn shr(self, bits: usize) -> Self::Output {
        let mut result = self.clone();
        result >>= bits;
        result
    }
}
