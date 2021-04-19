use core::ops::{Neg, Sub, SubAssign};

use ref_cast::RefCast;
#[cfg(feature = "ct-maybe")]
use subtle::{Choice, ConditionallySelectable};

use crate::{Digit, Modular, Montgomery, PrimeModular, SignedDoubleDigit, Unsigned, Wrapping};
use crate::numbers::{Array, Bits, Number};


/// Subtract with borrow:
#[inline]
pub fn sbb(a: Digit, b: Digit, acc: &mut SignedDoubleDigit) -> Digit {
    *acc += a as SignedDoubleDigit;
    *acc -= b as SignedDoubleDigit;
    let lo = *acc as Digit;
    *acc >>= Digit::BITS;
    lo
}

// pub fn sub_assign(a: &mut [Digit], b: &[Digit]) {
//     let mut borrow = 0;

//     let len = cmp::min(a.len(), b.len());
//     let (a_lo, a_hi) = a.split_at_mut(len);
//     let (b_lo, b_hi) = b.split_at(len);

//     for (a, b) in a_lo.iter_mut().zip(b_lo) {
//         *a = subb(*a, *b, &mut borrow);
//     }

//     if borrow != 0 {
//         for a in a_hi {
//             *a = subb(*a, 0, &mut borrow);
//             if borrow == 0 {
//                 break;
//             }
//         }
//     }

//     // note: we're _required_ to fail on underflow
//     assert!(
//         borrow == 0 && b_hi.iter().all(|x| *x == 0),
//         "Cannot subtract b from a because b is larger than a."
//     );
// }

// pub fn sub_assign_borrow(a: &mut [Digit], b: &[Digit]) -> Digit {
//     let mut borrow = 0;

//     let len = cmp::min(a.len(), b.len());
//     let (a_lo, a_hi) = a.split_at_mut(len);
//     let (b_lo, _b_hi) = b.split_at(len);

//     for (a, b) in a_lo.iter_mut().zip(b_lo) {
//         *a = subb(*a, *b, &mut borrow);
//     }

//     if borrow != 0 {
//         for a in a_hi {
//             *a = subb(*a, 0, &mut borrow);
//             if borrow == 0 {
//                 break;
//             }
//         }
//     }

//     borrow as Digit
// }

// A non-zero borrow (if a.len() == b.len()) is -1, which as unsigned is
// the same as "all bits set", i.e., 0xFFFF_FFFF for Digit = u32
pub fn sub_assign_borrow(a: &mut [Digit], b: &[Digit]) -> Digit {
    debug_assert!(a.len() >= b.len());
    let mut borrow = 0;

    let (a_lo, a_hi) = a.split_at_mut(b.len());

    for (a, b) in a_lo.iter_mut().zip(b) {
        *a = sbb(*a, *b, &mut borrow);
    }

    if borrow != 0 {
        for a in a_hi {
            *a = sbb(*a, 0, &mut borrow);
            #[cfg(not(feature = "ct-maybe"))] {
                if borrow == 0 {
                    break;
                }
            }
        }
    }

    borrow as Digit
}

// Subtraction in Unsigned / 2^M -- can forget borrows

/// TODO: This implementation (and the analogous one for Array) needs to be properly tested/fuzzed.
///
/// It's implemented more generally than for just T = Unsigned<D, E>
/// as we need that in `crate::arithmetic::divide::generic_div_rem.
///
/// There, we want to implement for any (dividend, divisor) pair.
/// The only real work is done for dividend > divisor, implying that dividend.len() >= divisor.len(),
/// and, where we're called, minuend >= subtrahend, and hence minuend.len() >= subtrahend.len().
///
/// This is needed to make the implementation of sub_assign_borrow (with dropped borrow) valid.
impl<T, const D: usize, const E: usize> SubAssign<&T> for Wrapping<Unsigned<D, E>>
where
    T: Number,
// impl<const D: usize, const E: usize> SubAssign<&Unsigned<D, E>> for Unsigned<D, E>
{
    fn sub_assign(&mut self, subtrahend: &T) {
    // fn sub_assign(&mut self, subtrahend: &Unsigned<D, E>) {
        // sub_assign_borrow(self.padded_number_mut(), subtrahend.padded_number());
        // sub_assign_borrow(self.padded_number_mut(), subtrahend.padded_number());
        sub_assign_borrow(&mut self.0, subtrahend);
    }
}

impl<const D: usize, const E: usize> Sub for &Wrapping<Unsigned<D, E>>
{
    type Output = Wrapping<Unsigned<D, E>>;

    fn sub(self, subtrahend: Self) -> Self::Output {
        let mut difference = self.clone();
        difference -= subtrahend;
        difference
    }
}

impl<const D: usize, const E: usize> Neg for &Wrapping<Unsigned<D, E>> {
    type Output = Wrapping<Unsigned<D, E>>;

    fn neg(self) -> Self::Output {
        &Self::Output::zero() - self
    }
}

impl<const D: usize, const E: usize> Unsigned<D, E> {
    pub fn wrapping_neg(&self) -> Self {
        Wrapping::ref_cast(self).neg().0
    }

    pub fn checked_sub(&self, subtrahend: &Self) -> Option<Self> {
        let mut difference = self.clone();
        let borrow = sub_assign_borrow(&mut difference, subtrahend);
        (borrow != 0).then(|| difference)
    }

    pub fn wrapping_sub_assign<T: Number>(&mut self, subtrahend: &T) {
        *Wrapping::ref_cast_mut(self) -= Wrapping::ref_cast(subtrahend);
    }

    pub fn wrapping_sub(&self, subtrahend: &Self) -> Self {
        let mut difference = self.clone();
        difference.wrapping_sub_assign(subtrahend);
        difference
    }
}

// Subtraction in Array / 2^M
// Exactly like Unsigned

/// TODO: See remark about SubAssign for Unsigned<D, E>
impl<T, const D: usize, const E: usize, const L: usize> SubAssign<&T> for Wrapping<Array<D, E, L>>
where
    T: Number,
// impl<const D: usize, const E: usize, const L: usize> SubAssign<&Array<D, E, L>> for Array<D, E, L>
{
    fn sub_assign(&mut self, other: &T) {
    // fn sub_assign(&mut self, other: &Self) {
        debug_assert!(self.len() >= other.len());
        sub_assign_borrow(&mut self.0, other);
    }
}

// impl<T, const D: usize, const E: usize, const L: usize> Sub<&T> for &Array<D, E, L>
// where
//     T: Number,
impl<const D: usize, const E: usize, const L: usize> Sub for &Wrapping<Array<D, E, L>>
{
    type Output = Wrapping<Array<D, E, L>>;

    // fn sub(self, other: &T) -> Self::Output {
    fn sub(self, other: Self) -> Self::Output {
        let mut difference = self.clone();
        difference -= other;
        difference
    }
}

impl<const D: usize, const E: usize, const L: usize> Array<D, E, L> {
    // pub fn wrapping_neg(&self) -> Self {
    //     Wrapping::ref_cast(self).neg().0
    // }

    pub fn wrapping_sub_assign<T: Number>(&mut self, subtrahend: &T) {
        *Wrapping::ref_cast_mut(self) -= Wrapping::ref_cast(subtrahend);
    }

    // pub fn wrapping_sub(&self, subtrahend: &Self) -> Self {
    //     let mut difference = self.clone();
    //     difference.wrapping_sub_assign(subtrahend);
    //     difference
    // }
}

// impl<T, const D: usize, const E: usize, const L: usize> SubAssign<&T> for Array<D, E, L>
// where
//     T: Number,
// {
//     fn sub_assign(&mut self, other: &T) {
//         sub_assign_borrow(self, other);
//     }
// }

// impl<T, const D: usize, const E: usize, const L: usize> Sub<&T> for &Array<D, E, L>
// where
//     T: Number,
// {
//     type Output = Array<D, E, L>;

//     fn sub(self, other: &T) -> Self::Output {
//         let mut difference = self.clone();
//         difference -= other;
//         difference
//     }
// }

// impl<T, const D: usize, const E: usize> Sub<&T> for &Modular<'_, D, E>
// where
//     T: Number,
// {
//     type Output = Unsigned<D, E>;

//     fn sub(self, other: &T) -> Self::Output {
//         let mut difference = self.clone();
//         difference -= other;
//         difference
//     }
// }

// Subtraction in Modular

impl<'a, 'n, const D: usize, const E: usize> SubAssign<&'a Self> for Modular<'n, D, E> {

    fn sub_assign(&mut self, subtrahend: &'a Self)  {
        debug_assert_eq!(**self.n, **subtrahend.n);

        #[allow(non_snake_case)]
        // G = 2p - 2^m, i.e., 2n
        let G = self.n.wrapping_add(&self.n);

        // step 3
        let borrow = sub_assign_borrow(&mut self.x, &subtrahend.x) as u8;

        #[cfg(not(feature = "ct-maybe"))]
        if borrow != 0 {
            self.x.wrapping_add(&G);
        }
        #[cfg(feature = "ct-maybe")] {
            self.x = Unsigned::conditional_select(
                &self.x,
                &self.x.wrapping_add(&G),
                Choice::from(borrow)
            )
        }
    }
}

impl<'a, 'n, const D: usize, const E: usize> Sub for &'a Modular<'n, D, E> {
    type Output = Modular<'n, D, E>;

    fn sub(self, subtrahend: Self) -> Self::Output {
        // debug_assert_eq!(**self.n, **summand.n);

        let mut difference = self.clone();
        difference -= subtrahend;

        difference
    }
}

impl<'a, 'p, const D: usize, const E: usize> Sub for &'a PrimeModular<'p, D, E> {
    type Output = PrimeModular<'p, D, E>;

    fn sub(self, subtrahend: Self) -> Self::Output {
        // debug_assert_eq!(**self.n, **summand.n);

        let mut difference = self.clone();
        *difference.as_modular_mut() -= subtrahend.as_modular();

        difference
    }
}

impl<'n, const D: usize, const E: usize> Neg for &Modular<'n, D, E> {
    type Output = Modular<'n, D, E>;

    fn neg(self) -> Self::Output {
        &Self::Output::zero(&self.n) - self
    }
}

impl<'p, const D: usize, const E: usize> Neg for &PrimeModular<'p, D, E> {
    type Output = PrimeModular<'p, D, E>;

    fn neg(self) -> Self::Output {
        &Self::Output::zero(&self.p) - self
    }
}

// Subtraction of Unsigned from Modular
// Simply delegates to subtraction in Modular, after partial reduction.

impl<'a, 'b, const D: usize, const E: usize, const F: usize, const G: usize> SubAssign<&'b Unsigned<F, G>> for Modular<'a, D, E> {
    fn sub_assign(&mut self, subtrahend: &'b Unsigned<F, G>) {
        *self -= &Modular { x: subtrahend.reduce(self.n), n: self.n }
    }
}

impl<'a, 'b, const D: usize, const E: usize, const F: usize, const G: usize> Sub<&'b Unsigned<F, G>> for Modular<'a, D, E> {
    type Output = Self;

    fn sub(self, subtrahend: &'b Unsigned<F, G>) -> Self::Output {

        let mut difference = self.clone();
        difference -= subtrahend;

        difference
    }
}


// Subtraction in Montgomery
// Exactly like in Modular

impl<'a, 'n, const D: usize, const E: usize> SubAssign<&'a Self> for Montgomery<'n, D, E> {

    fn sub_assign(&mut self, subtrahend: &'a Self)  {
        debug_assert_eq!(**self.n, **subtrahend.n);

        #[allow(non_snake_case)]
        // G = 2p - 2^m, i.e., 2n
        let G = self.n.wrapping_add(&self.n);

        // step 3
        let borrow = sub_assign_borrow(&mut self.y, &subtrahend.y) as u8;

        #[cfg(not(feature = "ct-maybe"))]
        if borrow != 0 {
            self.y.wrapping_add(&G);
        }
        #[cfg(feature = "ct-maybe")] {
            self.y = Unsigned::conditional_select(
                &self.y,
                &self.y.wrapping_add(&G),
                Choice::from(borrow)
            )
        }
    }
}

impl<'a, 'n, const D: usize, const E: usize> Sub for &'a Montgomery<'n, D, E> {
    type Output = Montgomery<'n, D, E>;

    fn sub(self, subtrahend: Self) -> Self::Output {
        // debug_assert_eq!(**self.n, **summand.n);

        let mut difference = self.clone();
        difference -= subtrahend;

        difference
    }
}


#[cfg(test)]
mod test {
    use crate::fixtures::*;

    #[test]
    fn sub_assign() {
        let f4 = crate::F4::PRIME.into_convenient();

        let one = Short64::one().modulo(&f4);
        assert_eq!(crate::F4::DIGIT - one.residue().digit(), 65536);

        let x = Short64::from(19900).modulo(&f4);
        let minus_x = crate::F4::DIGIT - x.residue().digit();
        assert_eq!(minus_x, 45637);
    }
}
