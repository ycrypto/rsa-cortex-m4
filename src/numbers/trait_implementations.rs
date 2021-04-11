use core::{cmp::Ordering, convert::TryFrom, fmt, ops::{Deref, DerefMut}};

use ref_cast::RefCast;

use super::{Array, Bits, Convenient, Digit, Number, NumberMut, Odd, Prime, Unsigned};
use crate::{Error, Result, Wrapping};


#[cfg(target_pointer_width = "32")]
impl Bits for usize {
    const BITS: usize = 32;
}

#[cfg(target_pointer_width = "64")]
impl Bits for usize {
    const BITS: usize = 64;
}

impl Bits for u32 {
    const BITS: usize = 32;
}

impl Bits for u128 {
    const BITS: usize = 128;
}

impl<T: Number> Bits for T {
    const BITS: usize = T::BITS;
}

impl<const D: usize, const E: usize> Deref for Unsigned<D, E> {
    type Target = [Digit];
    fn deref(&self) -> &Self::Target {
        Number::deref(self)
    }
}

impl<const D: usize, const E: usize> DerefMut for Unsigned<D, E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Number::deref_mut(self)
    }
}

impl<const D: usize, const E: usize, const L: usize> Deref for Array<D, E, L> {
    type Target = [Digit];
    fn deref(&self) -> &Self::Target {
        Number::deref(self)
    }
}

impl<const D: usize, const E: usize, const L: usize> DerefMut for Array<D, E, L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Number::deref_mut(self)
    }
}

// TODO: Maybe Deref to &[Digit] directly?
// And add some From/Into games.

impl<const D: usize, const E: usize> Deref for Convenient<D, E> {
    type Target = Unsigned<D, E>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const D: usize, const E: usize> DerefMut for Convenient<D, E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<const D: usize, const E: usize> Deref for Odd<D, E> {
    type Target = Unsigned<D, E>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const D: usize, const E: usize> DerefMut for Odd<D, E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<const D: usize> Deref for Prime<D> {
    type Target = Convenient<D, 0>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const D: usize> DerefMut for Prime<D> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: Number> Deref for Wrapping<T> {
    type Target = [Digit];
    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl<T: Number + NumberMut> DerefMut for Wrapping<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.0
    }
}

unsafe impl<T: Number> Number for Wrapping<T> {}
impl<T: Number + NumberMut> NumberMut for Wrapping<T> {}


impl<const D: usize, const E: usize> TryFrom<Unsigned<D, E>> for Odd<D, E> {
    type Error = Error;
    /// Enforces odd parity.
    fn try_from(unsigned: Unsigned<D, E>) -> Result<Self> {
        unsigned.is_odd().then(|| Odd(unsigned)).ok_or(Error)
    }
}

impl<'a, const D: usize, const E: usize> TryFrom<&'a Unsigned<D, E>> for &'a Odd<D, E> {
    type Error = Error;
    /// Enforces odd parity.
    fn try_from(unsigned: &'a Unsigned<D, E>) -> Result<Self> {
        unsigned.is_odd().then(|| Odd::ref_cast(unsigned)).ok_or(Error)
    }
}

impl<const D: usize, const E: usize> From<Odd<D, E>> for Unsigned<D, E> {
    fn from(odd: Odd<D, E>) -> Self {
        odd.0
    }
}

impl<const D: usize, const E: usize> TryFrom<Unsigned<D, E>> for Convenient<D, E> {
    type Error = Error;
    /// Enforces odd parity.
    fn try_from(unsigned: Unsigned<D, E>) -> Result<Self> {
        if !unsigned.is_odd() {
            return Err(Error);
        }

        if !unsigned.significant_digits().len() != Unsigned::<D, E>::DIGITS {
            panic!("logic error");
            // return Err(Error);
        }

        // if unsigned.leading_digit().unwrap().leading_zeros() != 0 {
        //     return Err(Error);
        // }
        let top_bit = unsigned.leading_digit().unwrap() >> (Digit::BITS - 1);
        if top_bit == 0 {
            return Err(Error);
        }

        Ok(Self(Odd(Unsigned::try_from_slice(&unsigned)?)))
    }
}

impl<const D: usize, const E: usize> From<Convenient<D, E>> for Unsigned<D, E> {
    fn from(convenient: Convenient<D, E>) -> Self {
        convenient.0.0
    }
}

// Since we store little-endian, comparison needs to start at the last
// digit, instead of at the first as the derived / default implementation would.
impl<const D: usize, const E: usize> Ord for Unsigned<D, E> {
    fn cmp(&self, other: &Self) -> Ordering {
        Number::cmp(self, other)
    }
}

impl<T, const D: usize, const E: usize> PartialOrd<T> for Unsigned<D, E>
where
    T: Number,
{
    /// This is *little endian* ordering, as opposed to the default
    /// ordering on arrays and slices!
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        // Some(generic_cmp_unsigned(self, other))
        Some(Number::cmp(self, other))
    }
}

impl<T, const D: usize, const E: usize, const L: usize> PartialOrd<T> for Array<D, E, L>
where
    T: Number,
{
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        Some(Number::cmp(self, other))
    }
}

impl<T, const D: usize, const E: usize> PartialEq<T> for Unsigned<D, E>
where
    T: Number,
{
    fn eq(&self, other: &T) -> bool {
        Number::eq(self, other)
    }
}

impl<T, const D: usize, const E: usize, const L: usize> PartialEq<T> for Array<D, E, L>
where
    T: Number,
{
    fn eq(&self, other: &T) -> bool {
        Number::eq(self, other)
    }
}

impl<T: Number, const D: usize, const E: usize> PartialEq<T> for Convenient<D, E> {
    fn eq(&self, other: &T) -> bool {
        Number::eq(&**self, other)
    }
}


impl<const D: usize, const E: usize> Default for Unsigned<D, E> {
    fn default() -> Self {
        Self { lo: [0; D], hi: [0; E] }
    }
}

impl<const D: usize, const E: usize, const L: usize> Default for Array<D, E, L> {
    fn default() -> Self {
        Self { lo: [[0; D]; L], hi: [[0; E]; L] }
    }
}

impl<const D: usize, const E: usize> fmt::Debug for Unsigned<D, E> {
    /// TODO: Do we want debug output to be big-endian bytes (as currently implemented)?
    /// Or stick with internal representation?
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&*self.to_bytes(), f)
    }
}

impl<const D: usize, const E: usize, const L: usize> fmt::Debug for Array<D, E, L> {
    /// TODO: Do we want debug output to be big-endian bytes (as currently implemented)?
    /// Or stick with internal representation?
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&*self.to_bytes(), f)
    }
}

