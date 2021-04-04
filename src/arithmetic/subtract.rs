use core::{cmp, ops::{Sub, SubAssign}};

use crate::{AsNormalizedLittleEndianWords, Digit, Modular, Odd, Product, SignedDoubleDigit, Unsigned};
use crate::numbers::Bits;


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

impl<T, const L: usize> SubAssign<&T> for Unsigned<L>
where
    T: AsNormalizedLittleEndianWords,
{
    fn sub_assign(&mut self, other: &T) {
        sub_assign(self, other);
    }
}

impl<T, const M: usize, const N: usize> SubAssign<&T> for Product<M, N>
where
    T: AsNormalizedLittleEndianWords,
{
    fn sub_assign(&mut self, other: &T) {
        sub_assign(self, other);
    }
}

// impl<T, const M: usize, const N: usize> SubAssign<T> for Product<M, N>
// where
//     T: AsNormalizedLittleEndianWords,
// {
//     fn sub_assign(&mut self, other: &T) {
//         sub_assign(self, other);
//     }
// }

