use core::ops::Mul;

use ref_cast::RefCast;

use crate::{Digit, DoubleDigit, Modular, Montgomery, Unsigned, Wrapping};
use crate::numbers::{Bits, Number, NumberMut, Product, Zero};

/// This just drops higher digits if `lhs * rhs` does not fit in a U.
pub(crate) fn wrapping_mul<U, V>(lhs: &U, rhs: &V) -> U
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

// #[inline]
// fn mac_with_carry(a: Digit, b: Digit, c: Digit, acc: &mut DoubleDigit) -> Digit {
//     *acc += a as DoubleDigit;
//     *acc += (b as DoubleDigit) * (c as DoubleDigit);
//     let lo = *acc as Digit;
//     *acc >>= Digit::BITS;
//     lo
// }

#[inline]
// a += b*c, handling carries via
fn add_product_into_digit(a: &mut Digit, b: Digit, c: Digit, acc: &mut DoubleDigit) {
    *acc += *a as DoubleDigit;
    *acc += (b as DoubleDigit) * (c as DoubleDigit);

    *a = *acc as Digit;
    *acc >>= Digit::BITS;
}

fn add_product_by_digit_into(a: &mut [Digit], b: &[Digit], c: Digit) -> Digit {
    debug_assert!(a.len() >= b.len());

    let mut acc: DoubleDigit = 0;

    let (a_lo, a_hi) = a.split_at_mut(b.len());

    for (a, b) in a_lo.iter_mut().zip(b) {
        // *a = adc(*a, *b, &mut carry);
        add_product_into_digit(a, *b, c, &mut acc);
    }


    if acc != 0 {
        for a in a_hi {
            add_product_into_digit(a, 0, c, &mut acc);
            if acc == 0 {
                break;
            }
        }
    }

    acc as Digit
}

fn carrying_mul<const D: usize, const E: usize>(lhs: &Unsigned<D, E>, rhs: &Unsigned<D, E>) -> Product<D, E> {

    let mut product = Product::default();

    for (j, c) in rhs.iter().enumerate() {
        let carry = add_product_by_digit_into(&mut product[j..], &lhs, *c);
        debug_assert_eq!(carry, 0);
    }

    product

    // THE BELOW WORKS, JUST NOT RAM-EFFICIENT
    // let lhs = Product::<D, E>::from_slice(lhs);
    // let rhs = Product::<D, E>::from_slice(rhs);
    // let product = wrapping_mul(&lhs, &rhs);
    // product

}

impl <const D: usize, const E: usize> Mul for &Wrapping<Unsigned<D, E>> {
    type Output = Wrapping<Unsigned<D, E>>;

    fn mul(self, other: Self) -> Self::Output {
        Wrapping(wrapping_mul(&self.0, &other.0))
    }
}

impl <const D: usize, const E: usize> Mul for &Unsigned<D, E> {

    type Output = Product<D, E>;

    /// *not* product-scanning implementation of multiplication, that overflowed
    fn mul(self, other: Self) -> Self::Output {
        carrying_mul(self, other)
        // let mut product = Product::default();
        // let mut accumulator = DoubleDigit::default();

        // for k in 0..2*(D + E) {
        //     // TODO: figure out proper loop (although maybe the compiler is smart enough?)
        //     for i in 0..self.len() {
        //         for j in 0..other.len() {
        //             if i + j == k {
        //                 accumulator += (self[i] as DoubleDigit) * (other[j] as DoubleDigit);
        //             }
        //         }
        //     }
        //     product[k] = accumulator as Digit;
        //     accumulator = accumulator >> Digit::BITS;
        // }
        // product
    }
}

impl <const D: usize, const E: usize> Unsigned<D, E> {
    pub fn wrapping_mul(&self, factor: &Self) -> Self {
        (Wrapping::ref_cast(self) * Wrapping::ref_cast(factor)).0
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

#[cfg(test)]
mod test {
    use crate::Long;
    use super::*;

    #[test]
    fn multiply() {
        // p = 100292567896662137431268955658963309646243393373296740296994110575772313854713
        // q =  92881035101327452495721684699134578528389025346126041237323965302769971181967
        #[cfg(any(target_pointer_width = "32", feature = "u32"))]
        let p = Long::<4>::from_slice(
            &[0x7cd022f9, 0xab998f98, 0x7ee8dd0c, 0xca27a8bd, 0xbd5ad74a, 0xdf02e961, 0x1af83b2a, 0xddbb94f1]);
        #[cfg(all(target_pointer_width = "64", not(feature = "u32")))]
        let p = Long::<2>::from_slice(
            &[0xab998f987cd022f9, 0xca27a8bd7ee8dd0c, 0xdf02e961bd5ad74a, 0xddbb94f11af83b2a]);
        #[cfg(any(target_pointer_width = "32", feature = "u32"))]
        let q = Long::<4>::from_slice(
            &[0x0721398f, 0xf0e5dc8a, 0x2d2b3f7d, 0xf0292b4e, 0x116bef81, 0x839d2553, 0xccf2db4c, 0xcd58cd8a]);
        #[cfg(all(target_pointer_width = "64", not(feature = "u32")))]
        let q = Long::<2>::from_slice(
            &[0xf0e5dc8a0721398f, 0xf0292b4e2d2b3f7d, 0x839d2553116bef81, 0xcd58cd8accf2db4c]);

        assert_eq!(p.to_be_bytes().as_be_bytes(), &[
            0xdd, 0xbb, 0x94, 0xf1, 0x1a, 0xf8, 0x3b, 0x2a, 0xdf, 0x2, 0xe9, 0x61, 0xbd, 0x5a, 0xd7, 0x4a,
            0xca, 0x27, 0xa8, 0xbd, 0x7e, 0xe8, 0xdd, 0xc, 0xab, 0x99, 0x8f, 0x98, 0x7c, 0xd0, 0x22, 0xf9]);
        assert_eq!(q.to_be_bytes().as_be_bytes(), &[
            0xcd, 0x58, 0xcd, 0x8a, 0xcc, 0xf2, 0xdb, 0x4c, 0x83, 0x9d, 0x25, 0x53, 0x11, 0x6b, 0xef, 0x81,
            0xf0, 0x29, 0x2b, 0x4e, 0x2d, 0x2b, 0x3f, 0x7d, 0xf0, 0xe5, 0xdc, 0x8a, 0x07, 0x21, 0x39, 0x8f]);

        #[cfg(any(target_pointer_width = "32", feature = "u32"))]
        let n = Long::<8>::from_slice(
            &[0x6125fa17, 0x98cfc7fb, 0x44473305, 0x5c5d5c9a, 0x791123bc, 0x657e9a1b, 0x6827494b, 0xbac18a9d,
              0xfda054d4, 0xa901c23e, 0x6af66649, 0xb25c8a46, 0x4755ee81, 0xa806189f, 0xb4613d3b, 0xb1dc20c7]);
        #[cfg(all(target_pointer_width = "64", not(feature = "u32")))]
        let n = Long::<4>::from_slice(
            &[0x98cfc7fb6125fa17, 0x5c5d5c9a44473305, 0x657e9a1b791123bc, 0xbac18a9d6827494b,
              0xa901c23efda054d4, 0xb25c8a466af66649, 0xa806189f4755ee81, 0xb1dc20c7b4613d3b]);

        assert_ne!(wrapping_mul(&p, &q).into_unsigned::<8,8>(), Unsigned::<8,8>::try_from_slice(&n).unwrap());
        assert_eq!(wrapping_mul(&p, &q).into_unsigned::<4,4>(), Unsigned::<4,4>::from_slice(&n[..(n.len()/2)]));

        assert_eq!(n.to_be_bytes().as_be_bytes(),
            &[0xb1, 0xdc, 0x20, 0xc7, 0xb4, 0x61, 0x3d, 0x3b, 0xa8, 0x06, 0x18, 0x9f, 0x47, 0x55, 0xee, 0x81,
              0xb2, 0x5c, 0x8a, 0x46, 0x6a, 0xf6, 0x66, 0x49, 0xa9, 0x01, 0xc2, 0x3e, 0xfd, 0xa0, 0x54, 0xd4,
              0xba, 0xc1, 0x8a, 0x9d, 0x68, 0x27, 0x49, 0x4b, 0x65, 0x7e, 0x9a, 0x1b, 0x79, 0x11, 0x23, 0xbc,
              0x5c, 0x5d, 0x5c, 0x9a, 0x44, 0x47, 0x33, 0x05, 0x98, 0xcf, 0xc7, 0xfb, 0x61, 0x25, 0xfa, 0x17]);

        assert_eq!(Product::<8,8>::from_slice(&n), n);
        // assert_eq!(&Product::<8,8>::from_slice(&n).to_be_bytes().as_be_bytes()[32..], &n.to_be_bytes().as_be_bytes()[32..]);
        // assert_eq!(&Product::<8,8>::from_slice(&n).to_be_bytes().as_be_bytes()[..64], &[0; 64]);

        assert_eq!(Product::<8,8>::from_slice(&n), carrying_mul(&p, &q));
        // assert_eq!(carrying_mul(&p, &q), Product::<8,8>::from_slice(&n));

        // let product = carrying_mul(&p, &q).to_be_bytes();
        // let product_be = product.as_be_bytes();
        // let reference = Product::<8,8>::from_slice(&n).to_be_bytes();
        // let reference_be = reference.as_be_bytes();
        // assert_eq!(&product_be[32..], &reference_be[32..]);
        // assert_eq!(&product_be[..32], &reference_be[..32]);
    }

}
