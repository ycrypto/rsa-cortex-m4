//! Modular arithmetic (for moduli that are either [`Convenient`] or word-sized powers-of-two).
//!
//! For `Modular`, we use incompletely reduced representations internally
//! (which can be implemented on a word-level), offering a complete reduction
//! for external use (which needs to be implemented on a bit-level).
//!
//! For `Wrapping<Unsigned>`, we implement operations "$\text{mod } 2^{32(D + E)}$",
//! that is, dropping all carries and borrows.
//!
//! This case does indeed have practical use, for instance,
//! to calculate $65537^{-1} \text{ mod }(p - 1)$ via Arazi's Lemma.

#![allow(unstable_name_collisions)]  // for Bits::BITS
#![allow(broken_intra_doc_links)]  // because `rustdoc` mistakes [x] for a link

use ref_cast::RefCast;
#[cfg(feature = "ct-maybe")]
use subtle::{Choice, ConditionallySelectable};
use zeroize::Zeroize;

use crate::{Convenient, Digit, ShortPrime, Unsigned};
use crate::numbers::Number;

mod shift;
mod add;
mod subtract;
mod montgomery;
mod multiply;
mod divide;


// pub enum Modulus<'n, const D: usize, const E: usize> {
//     Odd(&'n Odd<D, E>),
//     PowerOfTwo,  // typically, D or 2D
// }

/// Modular integer, corresponds to the residue class "modulo modulus".
///
/// For fixed modulus, this is a ring. If the modulus is prime, this is a field.
///
/// All constructors must enforce that `x < n` is the canonical residue class representative.
///
/// TODO: Maybe x and n don't need to have the same size.
/// E.g., would like to express x mod 2**{32*L}.
/// But nothing actually larger than this.
///
/// On the other hand, if `n` is substantially smaller (e.g., `e`, which has L = 1),
/// then it would be nice to project `x` down to that size.
#[derive(Clone)]
pub struct Modular<'n, const D: usize, const E: usize> {
    x: Unsigned<D, E>,
    // ring: ModularRing<'n, D, E>,
    n: &'n Convenient<D, E>,
}

#[derive(Copy, Clone, Debug)]
pub struct ModularRing<'n, const D: usize, const E: usize>(&'n Convenient<D, E>);

// impl<'n, const D: usize> ModularField<'n, D> {
//     /// Efficiently computes the inverse of $F4$.
//     pub fn f4_inverse() -> ShortModular<'n, D> {

//         todo!();
//     }
// }

#[derive(Clone)]
pub struct ModularField<'n, const D: usize>(&'n ShortPrime<D>);

impl<'n, const D: usize> ModularField<'n, D> {
    pub fn with_prime(p: &'n ShortPrime<D>) -> Self {
        Self(p)
    }

    /// Efficiently computes the inverse of $F4$.
    ///
    /// The formula is: $F_4^{-1} = \frac{1 + p*(-p^{0xFFFF}\text{ mod }65537)}{65537}$,
    /// where the calculation in brackets occurs
    pub fn f4_inverse(&self) -> ShortModular<'n, D> {
        let _f = self.0;
        let _e = crate::F4::DIGIT;
        // let convenient_e = Convenient(Odd(Short::<D>::from(e)));
        // let e_inverse = Wrapping(crate::F4).invert();
        // let numerator = Wrapping::ref_cast(&-f.modulo(&convenient_e).digit_pow(e - 2)) + 1)*(Wrapping;

        todo!();
    }
}

pub type ShortModular<'n, const D: usize> = Modular<'n, D, 0>;

impl<const D: usize, const E: usize> Zeroize for Modular<'_, D, E> {
    fn zeroize(&mut self) {
        self.x.zeroize();
    }
}

/// Montgomery representation of $[x]_{n} := x\text{ }(\text{mod }n)$,
/// as $[x \cdot 2^{-32L}]_n$.
///
/// This is an additive isomorphism `Modular<L>(_, n) -> Montgomery<L>(_, n)`.
/// "Montgomery multiplication" means the induced ring structure.
///
/// The "trick" is that reduction of excess summands after multiplication can
/// be calculated by a simple right shift instead of an actual modular division.
///
/// This needs to be balanced by the overhead of applying the additive isomorphism
/// and its inverse, which is negligible in certain situations, e.g., calculating
/// powers with large exponents.
///
/// Note: As described in [Incomplete reduction in modular arithmetic (2002)][yanik-savas-koc],
/// it is not necessary to reduce fully modulo `n` while calculating in the Montegomery
/// representation.
///
/// Also, as described in [Efficient software implementations of modular exponentiation
/// (2012)][gueron], using moduli with both the top and bottom bit set is particularly convenient.
///
/// [yanik-savas-koc]: https://api.semanticscholar.org/CorpusID:17543811
/// [gueron]: https://api.semanticscholar.org/CorpusID:7629541
#[allow(dead_code)]
#[derive(Clone)]
pub struct Montgomery<'n, const D: usize, const E: usize> {
    y: Unsigned<D, E>,
    n: &'n Convenient<D, E>,
}

pub type ShortMontgomery<'n, const D: usize> = Modular<'n, D, 0>;

#[cfg(feature = "ct-maybe")]
impl<const D: usize, const E: usize> subtle::ConditionallySelectable for Montgomery<'_, D, E> {
    fn conditional_select(a: &Self, b: &Self, c: subtle::Choice) -> Self {
        debug_assert_eq!(a.n.as_unsigned(), b.n.as_unsigned());

        Self {
            y: Unsigned::conditional_select(&a.y, &b.y, c),
            n: a.n
        }

    }
}

/// ## Reduction of unsigned integers
impl<const D: usize, const E: usize> Unsigned<D, E> {
    /// The associated residue class modulo n.
    ///
    /// Note that storage requirements of the residue class are the same
    /// as the modulus (+ reference to it), not the original integer.
    ///
    /// This uses incomplete reduction ([`Self::partially_reduce`]) for efficiency.
    pub fn modulo<'n, const F: usize, const G: usize>(&self, n: &'n Convenient<F, G>) -> Modular<'n, F, G> {
        Modular { x: self.reduce(n), n }
    }

    ///// A noncanonical representative of the associated residue class modulo n.
    /////
    ///// The "incomplete reduction" modulo $w^{D + E}$, where $w$ is the digit size
    ///// $2^{\text{BITS}}$, i.e., the word size of the machine.
    /////
    ///// Cf. [`Modular`].
    //pub fn partially_reduce<const F: usize, const G: usize>(&self) -> Unsigned<F, G> {
    //    use crate::numbers::NumberMut;
    //    Unsigned::from_slice(&self[..(F + G)])
    //}

    /// The canonical (completely) reduced representative of the associated residue class modulo $n$.
    ///
    /// Cf. [`Modular`].
    pub fn reduce<const F: usize, const G: usize>(&self, n: &Unsigned<F, G>) -> Unsigned<F, G> {
        let remainder = self % n;
        assert!(!remainder.is_zero());
        remainder
    }

    // /// For convenient moduli, complete reduction is just incomplete reduction followed
    // /// by a conditional subtraction.
    // pub fn conveniently_reduce<const F: usize, const G: usize>(self, n: &Convenient<F, G>) -> Unsigned<F, G> {
    //     self.modulo(n).canonical_lift()
    // }

}

impl<'n, const D: usize, const E: usize> Modular<'n, D, E> {
    pub fn zero(n: &'n Convenient<D, E>) -> Self {
        Self { x: crate::numbers::Number::zero(), n }
    }

    pub fn digit_pow(&self, _exponent: crate::Digit) -> Self {
        todo!();
    }

    pub fn inverse(&self) -> Self {
        todo!();
    }

    /// The canonical representative of this residue class.
    ///
    /// This is like [`lift`][lift] in GP/PARI
    ///
    /// By virtue of our moduli's convenience, this is just a conditional subtraction.
    /// [lift]: https://pari.math.u-bordeaux.fr/dochtml/html/Conversions_and_similar_elementary_functions_or_commands.html#se:lift
    // pub fn lift<const L: usize>(self) -> Unsigned<L> {
    //     // TODO: if L < N (or rather, self.modulo.len()), then lift and project maybe? nah
    //     self.x.into_unsigned()
    pub fn canonical_lift(&self) -> Unsigned<D, E> {


        #[cfg(not(feature = "ct-maybe"))] {
             let residue = self.x.clone();

             if self.x >= **self.n {
                 residue.wrapping_sub(self.n)
             } else {
                 residue
             }
         }

        #[cfg(feature = "ct-maybe")] {
            use subtle::ConstantTimeLess;
            let must_reduce = !self.x.ct_lt(self.n.as_unsigned());

            Unsigned::<D, E>::conditional_select(
                &self.x,
                &self.x.wrapping_sub(self.n),
                must_reduce,
            )
        }

    }

    pub fn to_montgomery(&self) -> Montgomery<'n, D, E> {
        montgomery::to_montgomery(self)
    }

    // pub fn to_the(self, exponent: & impl Into<Unsigned<L>>) -> Self {
    pub fn power<const F: usize, const G: usize>(&self, exponent: &Unsigned<F, G>) -> Self {
        // TODO: If exponent is a small prime, special-case.
        // self.to_montgomery().power(exponent).to_modular()
        self.to_montgomery().power(exponent).to_modular()
    }
}

impl<'n, const D: usize, const E: usize> Montgomery<'n, D, E> {
    pub fn to_modular(&self) -> Modular<'n, D, E> {
        montgomery::to_modular(self)
    }

    pub fn one(&self) -> Self {
        Self { y: super::arithmetic::montgomery::R_mod_p(&self.n), n: self.n }
    }

    pub fn power<const F: usize, const G: usize>(&self, exponent: &Unsigned<F, G>) -> Self {
        use crate::numbers::Bits;
        let mut x = self.one();

        for i in (0..(F + G)).rev() {
            for j in (0..Digit::BITS).rev() {
                x = &x * &x;

                #[cfg(not(feature = "ct-maybe"))] {
                    if (exponent[i] & (1 << j)) != 0 {
                        x *= self;
                    }
                }

                #[cfg(feature = "ct-maybe")] {
                    x = Self::conditional_select(
                        &x,
                        &(&x * self),
                        Choice::from(((exponent[i] >> j) & 1) as u8),
                    )
                }
            }
        }
        x
    }
}

impl<const D: usize, const E: usize> From<Modular<'_, D, E>> for Unsigned<D, E> {
    fn from(class: Modular<'_, D, E>) -> Self {
        class.canonical_lift()
    }
}

#[repr(transparent)]
#[derive(Clone, Debug, Default, PartialEq, RefCast)]
/// Intentionally-wrapped arithmetic.
///
/// We can't use `core::num::Wrapping` due to type coherence clashing
/// with our usage requirements.
///
/// The idea is that `T` is [`Number`], and we wrap around $2^N$ where `N = T::BITS`.
pub struct Wrapping<T>(pub T);

#[cfg(test)]
mod test {
    use crate::fixtures::*;

    #[test]
    fn power() {
        let a = q256().into_unsigned();
        // println!("a = {:?}", a);
        let p = p256().into_convenient();
        // println!("p = {:?}", **p);

        let modular = a.modulo(&p);

        // sanity
        assert!(&a <= p.as_unsigned());
        assert_eq!(modular.x, a);
        // println!("modular.x = {:?}", modular.x);
        // println!("modular.n = {:?}", **modular.n);
        assert_eq!(modular.canonical_lift(), a);

        // a^1
        let itself = modular.power(&Short64::from(1));
        assert_eq!(itself.canonical_lift(), a);

        // a^2
        let squared = modular.power(&Short64::from(2));
        // GP/PARI: `hex(lift(Mod(q, p)^2))`
        let expected = Short256::from_bytes(&hex!(
            "31d9c0a7a9c089c4a8086da5fe743c1626423611222b7919f843e58138913299"));
        assert_eq!(squared.canonical_lift(), expected);

        // a^37
        let result = modular.power(&Short64::from(37));
        let expected = Short256::from_bytes(&hex!(
            "731c4d5e69ac480ea2874bc44e05e99d2827a5b651f3ab199945fd1635968a9e"));
        assert_eq!(result.canonical_lift(), expected);

        // a^F4
        let result = modular.power(&Short64::from(crate::F4::DIGIT));
        let expected = Short256::from_bytes(&hex!(
            "274f34228885e3cbc71cc20bcc25618d2589656efd14557a12b02ff89920d17a"));
        assert_eq!(result.canonical_lift(), expected);

        // a^c
        let c = c256();
        let result = modular.power(&c);
        let expected = Short256::from_bytes(&hex!(
            "a0aa5df2567cc062788a64714276c5373f2240589874d2143401dd9c3c2efae1"));
        assert_eq!(result.canonical_lift(), expected);
    }
}
