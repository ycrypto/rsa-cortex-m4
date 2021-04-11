//! All things $F4$

use crate::{Convenient, Digit, Odd, Prime, Short, Unsigned};

/// The fourth Fermat prime, $2^{16} + 1$ (used as public exponent $e$).
///
/// This library only implements RSA keys with public exponent `e = 65537 = 0x10001 = u16::MAX + 2`.
///
/// An example recommendation to do so is RFC 4871: <https://www.ietf.org/rfc/rfc4871.txt>,
/// more generally, there seems no need to have too many knobs to turn.
pub struct F4 {}

impl F4 {
    pub const DIGIT: Digit = 0x1_0001;
    pub const PRIME: Prime<1, 0> = Prime(Convenient(Odd(Short::from_digit(Self::DIGIT))));

    pub fn prime() -> Prime<1, 0> {
        Prime(Convenient(Odd(Short::from(Self::DIGIT))))
    }

    pub fn wrapping_inv<const D: usize, const E: usize> () -> Unsigned<D, E> {
        Unsigned::from(Self::DIGIT).wrapping_inv().unwrap()
        // crate::arithmetic::divide::wrapping_invert_odd(Self::Prime.as_ref().as_ref())

    }

    /// The inverse of $F4$ modulo other primes is used in RSA,
    /// and deserves an optimized implementation.
    pub fn inv_mod<const D: usize>(p: &Prime<D, 0>) -> Odd<D, 0> {
        let f = p.as_ref().as_ref();
        let f_mod_e = f.clone().modulo(Self::PRIME.as_ref());

        let minus_f_inv_mod_e: Digit = (-&f_mod_e.inverse()).canonical_lift().digit();

        let numerator: Short<D> = (f * minus_f_inv_mod_e).wrapping_add(&crate::Unsigned::<D, 1>::from(1)).to_unsigned().unwrap();
        //
        let inverted_denominator = Self::wrapping_inv();

        let d = numerator.wrapping_mul(&inverted_denominator);
        Odd(d)
    }
}


#[cfg(test)]
mod test {
    // use super::*;
    // use hex_literal::hex;

    #[test]
    fn modular_inverses() {
        let _p = crate::fixtures::p256();
        // let x = F4::inv_mod(&p);
        // // expect: 69839204130490714648989446105377245866084955725424467658481777077780812173086
        // // via GP/PARI: printf("%x", lift(1/Mod(e, p)))

        // assert_eq!(&*x.to_bytes(), &hex!("9a6796b73305ab0616980b76d18a61a3a61469efd3614b1518a5ed95cd4c8f1e"));
    }

}

