//! Unsigned and Modular.
//!
//! TODO: Note that we also have use for `Mod(Unsigned<L>, 2^{32*L})`,
//! for instance to calculate `1/e (mod p - 1)`.

#![allow(unstable_name_collisions)]  // for Bits::BITS

use zeroize::Zeroize;

use crate::{Digit, NonZeroOdd, Unsigned};
use crate::numbers::AsNormalizedLittleEndianWords;

mod add;
mod subtract;
mod shift;
mod multiply;
mod divide;


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
pub struct Modular<'n, const L: usize> {
    x: Unsigned<L>,
    n: &'n NonZeroOdd<L>,
}

impl<const L: usize> Zeroize for Modular<'_, L> {
    fn zeroize(&mut self) {
        self.x.zeroize();
    }
}

impl<const L: usize> Unsigned<L> {
    /// The associated residue class modulo n.
    ///
    /// Note that storage requirements of the residue class are the same
    /// as the modulus (+ reference to it), not the original integer.
    pub fn modulo<const N: usize>(self, n: &NonZeroOdd<N>) -> Modular<'_, N> {
        let reduced_residue_class_representative = &self % &**n;
        Modular { x: reduced_residue_class_representative, n }
        // let mut modular = Modular { x: self, n };
        // reduce_modulo(0, &mut modular.x, n);
        // modular
    }

    /// The canonical representative of the associated residue class modulo n.
    pub fn reduce(self, n: &NonZeroOdd<L>) -> Self {
        self.modulo(n).lift()
    }

}

// pub fn chinese_remainder_theorem

impl<const N: usize> Modular<'_, N> {
    pub fn inverse(&self) -> Self {
        todo!();
    }

    /// The canonical representative of this residue class.
    ///
    /// This is like [`lift`][lift] in GP/PARI
    ///
    /// [lift]: https://pari.math.u-bordeaux.fr/dochtml/html/Conversions_and_similar_elementary_functions_or_commands.html#se:lift
    pub fn lift<const L: usize>(self) -> Unsigned<L> {
        // TODO: if L < N (or rather, self.modulo.len()), then lift and project maybe? nah
        self.x.into_unsigned()
    }

    // pub fn to_the(self, exponent: & impl Into<Unsigned<L>>) -> Self {
    pub fn power(self, exponent: & impl Into<Unsigned<N>>) -> Self {
        todo!();
    }
}

impl<const L: usize> From<Modular<'_, L>> for Unsigned<L> {
    fn from(class: Modular<'_, L>) -> Self {
        class.lift()
    }
}

fn reduce_modulo_once<const L: usize>(c: Digit, x: &mut Unsigned<L>, n: &NonZeroOdd<L>) {
    todo!();
    // if c > 0 || *x >= *n {
    //     sub_assign_unchecked(x, n);
    // }
}

fn reduce_modulo<const L: usize>(c: Digit, x: &mut Unsigned<L>, n: &NonZeroOdd<L>) {
    todo!();
}

#[cfg(test)]
mod test {
    use super::*;
}
