use core::ops::{Add, AddAssign};

use crate::{Digit, DoubleDigit, Modular, NonZeroOdd, Unsigned};
use crate::numbers::Bits;

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
    // reduce_modulo(c, &mut r, n);

    // 3. done
    r
}

impl<'a, 'b, const L: usize> Add<&'b Unsigned<L>> for Modular<'a, L> {
    type Output = Self;

    fn add(self, rhs: &'b Unsigned<L>) -> Self {
        todo!();
    }
}

//
// from num-bigint
//


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

