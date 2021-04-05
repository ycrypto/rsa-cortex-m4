use core::ops::{Add, AddAssign};

use crate::{Digit, DoubleDigit, Modular, Montgomery, Unsigned};
use crate::numbers::Bits;

/// Intention is to replace this with the UMAAL assembly instruction on Cortex-M4.
///
/// Operation: `(hi, lo) = m*n + hi + lo`
///
/// This works, because `(2^32 - 1)^2 + 2*(2^32 - 1) = 2^64 - 1`.
#[allow(dead_code)]
pub fn umaal(hi: &mut u32, lo: &mut u32, m: u32, n: u32) {
    let result = ((m as u64) * (n as u64)) + (*hi as u64) + (*lo as u64);
    *hi = (result >> u32::BITS) as u32;
    *lo = result as u32;
}

/// place (a + b + c) in r with carry c
#[allow(dead_code)]
pub fn addc(a: u32, b: u32, c: &mut u32, r: &mut u32) {
    *r = a;
    umaal(c, r, 1, b);
}

// fn add_modulo<const L: usize>(a: &Unsigned<L>, b: &Unsigned<L>, n: &Odd<L>) -> Unsigned<L> {
//     let mut r = Unsigned::<L>::default();
//     let mut c = 0;

//     // 1. sum up term-by-term
//     for i in 0..L {
//         // let sum = (a.0[i] as u64) + (b.0[i] as u64) + c as u64;
//         // r.0[i] = sum as u32;
//         // c = (sum >> 32) as u32;
//         addc(a.0[i], b.0[i], &mut c, &mut r.0[i]);
//     }

//     // for ((ai, bi), ri) in (a.as_ref().iter().zip(b.as_ref().iter())).zip(r.as_mut().iter()) {
//     //     let sum = (*ai as u64) + (*bi as u64) + c as u64;
//     //     *ri = sum as u32;
//     //     todo!();
//     // }

//     // 2. reduce modulo n
//     // reduce_modulo(c, &mut r, n);

//     // 3. done
//     r
// }

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

// This is perhaps too general - we always use equal length slices I believe.
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



// Addition in Unsigned / 2^M

impl<const D: usize, const E: usize> AddAssign<&Unsigned<D, E>> for Unsigned<D, E> {
    fn add_assign(&mut self, summand: &Self) {
        add_assign_carry(self, summand);
    }
}

impl<const D: usize, const E: usize> Add for &Unsigned<D, E> {
    type Output = Unsigned<D, E>;

    fn add(self, summand: Self) -> Self::Output {

        let mut sum = self.clone();
        sum += &summand;

        sum
    }
}



// Addition in Modular

impl<'a, 'n, const D: usize, const E: usize> AddAssign<&'a Self> for Modular<'n, D, E> {

    fn add_assign(&mut self, summand: &'a Self)  {
        debug_assert_eq!(**self.n, **summand.n);

        #[allow(non_snake_case)]
        let F = -&**self.n;

        // step 3
        let carry = add_assign_carry(&mut self.x, &summand.x);

        // TODO: consider making this constant time.
        if carry != 0 {
            add_assign_carry(&mut self.x, &F);
        }
    }
}

impl<'a, 'n, const D: usize, const E: usize> Add for &'a Modular<'n, D, E> {
    type Output = Modular<'n, D, E>;

    fn add(self, summand: Self) -> Self::Output {
        // debug_assert_eq!(**self.n, **summand.n);

        let mut sum = self.clone();
        sum += summand;

        sum
    }
}

// Addition of Unsigned to Modular
// Simply delegates to addition in Modular, after partial reduction.

impl<'a, 'b, const D: usize, const E: usize, const F: usize, const G: usize> AddAssign<&'b Unsigned<F, G>> for Modular<'a, D, E> {
    fn add_assign(&mut self, summand: &'b Unsigned<F, G>) {
        *self += &Modular { x: summand.partially_reduce(), n: self.n }
    }
}

impl<'a, 'b, const D: usize, const E: usize, const F: usize, const G: usize> Add<&'b Unsigned<F, G>> for Modular<'a, D, E> {
    type Output = Self;

    fn add(self, summand: &'b Unsigned<F, G>) -> Self::Output {

        let mut sum = self.clone();
        sum += summand;  // this does a spurious `reduce` on our reduced other.x

        sum
    }
}


// Addition in Montgomery
// Exactly like addition in Modular

impl<'a, 'n, const D: usize, const E: usize> AddAssign<&'a Self> for Montgomery<'n, D, E> {

    fn add_assign(&mut self, summand: &'a Self)  {
        debug_assert_eq!(**self.n, **summand.n);

        #[allow(non_snake_case)]
        let F = -&**self.n;

        // step 3
        let carry = add_assign_carry(&mut self.y, &summand.y);

        if carry != 0 {
            add_assign_carry(&mut self.y, &F);
        }
    }
}

impl<'a, 'n, const D: usize, const E: usize> Add for &'a Montgomery<'n, D, E> {
    type Output = Montgomery<'n, D, E>;

    fn add(self, summand: Self) -> Self::Output {
        // debug_assert_eq!(**self.n, **summand.n);

        let mut sum = self.clone();
        sum += summand;

        sum
    }
}

