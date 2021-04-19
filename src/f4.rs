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
    /// NOTE!!! F4 is *not* convenient, it's only a 17-bit number, whereas
    /// Convenient<1, 0> would mean either 31-bit or 63-bit.
    pub const SHORT: Short<1> = Short::from_digit(Self::DIGIT);
    pub const PRIME: Prime<1, 0> = Prime(Convenient(Odd(Short::from_digit(Self::DIGIT))));

    pub fn minus_one() -> Short<1> {
        Short::from(Self::DIGIT - 1)

    }

    pub fn prime() -> Prime<1, 0> {
        Prime(Convenient(Odd(Short::from(Self::DIGIT))))
    }

    pub fn wrapping_inv<const D: usize, const E: usize> () -> Unsigned<D, E> {
        Unsigned::from(Self::DIGIT).wrapping_inv().unwrap()
    }

    /// The inverse of $F4$ modulo other primes is used in RSA,
    /// and deserves an optimized implementation.
    ///
    /// This is Arazi's lemma.
    ///
    /// TODO: Prove (disprove?) that calculating the inverse of `p_mod_e` via PrimeModular's inversion
    /// is valid, as F4 is not actually "convenient".
    ///
    /// N.B.: We do have a test that the inverse is correct (see test `inv_mod_e`).
    // pub fn inv_mod<const D: usize>(p: &Prime<D, 0>) -> Odd<D, 0> {
    pub fn inv_mod<const D: usize>(p: &Unsigned<D, 0>) -> Odd<D, 0> {
        // p = f
        // let p = p.as_unsigned();
        let p_mod_e = p.clone().modulo_prime(&Self::PRIME);

        // inverse here is iffy (coming from prime/convenient, which we're not
        let minus_p_inv_mod_e: Digit = Self::DIGIT - p_mod_e.inverse().canonical_lift().digit();

        let numerator: crate::Unsigned<D, 1> =
            (p * &Short::<D>::from(minus_p_inv_mod_e))
            .to_unsigned::<D, 1>().unwrap()
            .wrapping_add(&crate::Unsigned::<D, 1>::from(1));
            // .to_unsigned().expect("fits");
        //
        let inverted_denominator = Self::wrapping_inv();

        let d = numerator.wrapping_mul(&inverted_denominator);
        Odd(d.to_unsigned().unwrap())
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use hex_literal::hex;

    #[test]
    fn modular_inverses() {
        // let e = F4::DIGIT;
        let p = crate::fixtures::p256();

        let p_mod_e = p.modulo_prime(&F4::PRIME);

        assert_eq!(p_mod_e.residue(), &Short::<1>::from_slice(&[49818]));
        assert_eq!(p_mod_e.canonical_lift().digit(), 49818);

        // // TODO TODO
        // let minus_p_mod_e = crate::F4::DIGIT - p_mod_e.residue().digit();
        // assert_eq!(minus_p_mod_e, 45637);

        // TODO TODO
        assert_eq!(p_mod_e.inverse().canonical_lift().digit(), 19900);

        let minus_p_inv_mod_e = crate::F4::DIGIT - p_mod_e.inverse().canonical_lift().digit();
        assert_eq!(minus_p_inv_mod_e, 45637);

        let minus_p_inv_mod_e = crate::F4::DIGIT - p_mod_e.inverse().residue().digit();
        assert_eq!(minus_p_inv_mod_e, 45637);

        // let numerator = (p * &Short::<D>::from(minus_p_inv_mod_e))
        //     .to_unsigned().unwrap()
        //     .wrapping_add(&Unsigned::from(1));

        // Now for the actual test
        let modular_inverse = F4::inv_mod(&p);

        // expect: 69839204130490714648989446105377245866084955725424467658481777077780812173086
        // via GP/PARI: printf("%x", lift(1/Mod(e, p)))
        assert_eq!(&*modular_inverse.to_bytes(), &hex!("9a6796b73305ab0616980b76d18a61a3a61469efd3614b1518a5ed95cd4c8f1e"));


        // assert_eq!(&*x.to_bytes(), &hex!("9a6796b73305ab0616980b76d18a61a3a61469efd3614b1518a5ed95cd4c8f1e"));
    }

    #[test]
    #[cfg(feature = "extended-testing")]
    // possibly lengthy test, would be unneccessary to run every time.
    fn inv_mod_e() {
        let e = F4::DIGIT;
        let f4 = F4::PRIME;
        for i in 3..e {
            let maybe_inverse: Short<1> = Short::<1>::from(i).modulo_prime(&f4).inverse().canonical_lift();//.digit();

            let maybe_one: crate::Long<1> = (f4.as_unsigned() * &maybe_inverse).to_unsigned().unwrap();
            let remainder = (maybe_one % f4.as_unsigned()).digit();
            assert_eq!(remainder, 0);
        }
    }
}

