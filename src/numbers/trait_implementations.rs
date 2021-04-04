use core::{cmp::Ordering, convert::TryFrom, fmt, ops::{Deref, DerefMut}};

use super::{AsNormalizedLittleEndianWords, Digit, DoubleDigit, NonZeroOdd, Prime, Product, Unsigned};
use crate::{Error, Result};


impl super::Bits for Digit {
    const BITS: usize = 32;
}

impl super::Bits for DoubleDigit {
    const BITS: usize = 64;
}

// Unfortunately, implementing Deref for <T: AsNormalizedLittleEndianWords>
// leads to "conflicting implementations"
impl<const L: usize> Deref for Unsigned<L> {
    type Target = [Digit];
    fn deref(&self) -> &Self::Target {
        self.words()
    }
}

impl<const L: usize> DerefMut for Unsigned<L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.words_mut()
    }
}

impl<const M: usize, const N: usize> Deref for Product<M, N> {
    type Target = [Digit];
    fn deref(&self) -> &Self::Target {
        self.words()
    }
}

impl<const M: usize, const N: usize> DerefMut for Product<M, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.words_mut()
    }
}

impl<const L: usize> Deref for NonZeroOdd<L> {
    type Target = Unsigned<L>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const L: usize> DerefMut for NonZeroOdd<L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<const L: usize> Deref for Prime<L> {
    type Target = NonZeroOdd<L>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const L: usize> DerefMut for Prime<L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<const L: usize> TryFrom<Unsigned<L>> for NonZeroOdd<L> {
    type Error = Error;
    /// Enforces positivity and oddity.
    fn try_from(unsigned: Unsigned<L>) -> Result<Self> {
        use super::Zero;
        // non-zero
        if unsigned.is_zero() {
            return Err(Error);
        }
        // odd
        if unsigned.0[0] & 1 == 0 {
            return Err(Error);
        }
        Ok(Self(unsigned))
    }
}

impl<const L: usize> From<NonZeroOdd<L>> for Unsigned<L> {
    fn from(nonzero_odd: NonZeroOdd<L>) -> Self {
        nonzero_odd.0
    }
}

/// This is *little endian* ordering, as opposed to the default
/// ordering on arrays and slices!
fn cmp_unsigned<const M: usize, const N: usize>(m: &Unsigned<M>, n: &Unsigned<N>) -> Ordering {
    let l_m = m.len();
    let l_n = n.len();
    match l_m.cmp(&l_n) {
        Ordering::Equal => {}
        not_equal => return not_equal,
    }

    for i in (0..l_m).rev() {
        match m.words()[i].cmp(&n.words()[i]) {
            Ordering::Equal => (),
            not_equal => return not_equal
        }
    }
    Ordering::Equal
}

// Since we store little-endian, comparison needs to start at the last
// digit, instead of at the first as the derived / default implementation would.
impl<const L: usize> Ord for Unsigned<L> {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_unsigned(self, other)
    }
}

impl<const M: usize, const N: usize> PartialOrd<Unsigned<N>> for Unsigned<M> {
    /// This is *little endian* ordering, as opposed to the default
    /// ordering on arrays and slices!
    fn partial_cmp(&self, other: &Unsigned<N>) -> Option<Ordering> {
        Some(cmp_unsigned(self, other))
    }
}

impl<const M: usize, const N: usize> PartialEq<Unsigned<N>> for Unsigned<M> {
    fn eq(&self, other: &Unsigned<N>) -> bool {
        // self.words() == other.words()
        **self == **other
    }
}

impl<const L: usize> PartialEq<NonZeroOdd<L>> for Unsigned<L> {
    fn eq(&self, other: &NonZeroOdd<L>) -> bool {
        *self == **other//.words() == other.words()
    }
}

impl<const L: usize> PartialEq<Unsigned<L>> for NonZeroOdd<L> {
    fn eq(&self, other: &Unsigned<L>) -> bool {
        **self == *other
    }
}

impl<const L: usize> PartialOrd<NonZeroOdd<L>> for Unsigned<L> {
    fn partial_cmp(&self, other: &NonZeroOdd<L>) -> Option<core::cmp::Ordering> {
        self.partial_cmp(&other.0)
    }
}

impl<const L: usize> PartialOrd<Unsigned<L>> for NonZeroOdd<L> {
    fn partial_cmp(&self, other: &Unsigned<L>) -> Option<core::cmp::Ordering> {
        self.0.partial_cmp(other)
    }
}

impl<const L: usize> Default for Unsigned<L> {
    fn default() -> Self {
        Self([0; L])
    }
}

impl<const L: usize> fmt::Debug for Unsigned<L> {
    /// TODO: Do we want debug output to be big-endian bytes (as currently implemented)?
    /// Or stick with internal representation?
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.to_be_bytes().as_be_bytes(), f)
    }
}

