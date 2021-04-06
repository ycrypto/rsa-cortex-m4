use core::{cmp::Ordering, convert::TryFrom, fmt, ops::{Deref, DerefMut}};

use super::{Array, Bits, Convenient, Digit, DoubleDigit, Number, NumberMut, Prime, Unsigned};
use crate::{Error, Result};


impl Bits for Digit {
    const BITS: usize = 32;
}

impl Bits for DoubleDigit {
    const BITS: usize = 64;
}

impl<const D: usize, const E: usize> Bits for Unsigned<D, E> {
    const BITS: usize = Digit::BITS * (D + E);
}

impl<const D: usize, const E: usize, const L: usize> Bits for Array<D, E, L> {
    const BITS: usize = Digit::BITS * (D + E) * L;
}

// // Unfortunately, implementing Deref for <T: AsNormalizedLittleEndianWords>
// // leads to "conflicting implementations"
// impl<const L: usize> Deref for Unsigned<L> {
//     type Target = [Digit];
//     fn deref(&self) -> &Self::Target {
//         self.words()
//     }
// }

// impl<const L: usize> DerefMut for Unsigned<L> {
//     fn deref_mut(&mut self) -> &mut Self::Target {
//         self.words_mut()
//     }
// }

impl<const D: usize, const E: usize> Deref for Unsigned<D, E> {
    type Target = [Digit];
    fn deref(&self) -> &Self::Target {
        self.number()
    }
}

impl<const D: usize, const E: usize> DerefMut for Unsigned<D, E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.padded_number_mut()
    }
}

impl<const D: usize, const E: usize, const L: usize> Deref for Array<D, E, L> {
    type Target = [Digit];
    fn deref(&self) -> &Self::Target {
        self.number()
    }
}

impl<const D: usize, const E: usize, const L: usize> DerefMut for Array<D, E, L> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.padded_number_mut()
    }
}

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

// impl<const D: usize, const E: usize> TryFrom<Unsigned<D, E>> for Odd<D, E> {
//     type Error = Error;
//     /// Enforces odd parity.
//     fn try_from(unsigned: Unsigned<D, E>) -> Result<Self> {
//         use super::Zero;
//         // non-zero (so we can index in next step)
//         if unsigned.is_zero() {
//             return Err(Error);
//         }
//         // odd
//         if unsigned[0] & 1 == 0 {
//             return Err(Error);
//         }
//         Ok(Self(unsigned))
//     }
// }

// impl<const D: usize, const E: usize> From<Odd<D, E>> for Unsigned<D, E> {
//     fn from(odd: Odd<D, E>) -> Self {
//         odd.0
//     }
// }

impl<const D: usize, const E: usize> TryFrom<Unsigned<D, E>> for Convenient<D, E> {
    type Error = Error;
    /// Enforces odd parity.
    fn try_from(unsigned: Unsigned<D, E>) -> Result<Self> {
        // non-zero (so we can index in next step)
        let (l, c) = (unsigned.len(), D + E);
        if c == 0 || l < c {
            return Err(Error);
        }
        if unsigned[0] & 1 == 0 {
            return Err(Error);
        }
        if unsigned.leading_digit().unwrap() >> (Digit::BITS - 1) == 0 {
            return Err(Error);
        }
        Ok(Self(unsigned))
    }
}

impl<const D: usize, const E: usize> From<Convenient<D, E>> for Unsigned<D, E> {
    fn from(convenient: Convenient<D, E>) -> Self {
        convenient.0
    }
}

/// This is *little endian* ordering, as opposed to the default
/// ordering on arrays and slices!
// fn cmp_unsigned<const M: usize, const N: usize>(m: &Unsigned<M>, n: &Unsigned<N>) -> Ordering {
fn generic_cmp_unsigned<M, N>(m: &M, n: &N) -> Ordering
where
    M: Number,
    N: Number,
{
    let l_m = m.len();
    let l_n = n.len();
    match l_m.cmp(&l_n) {
        Ordering::Equal => {}
        not_equal => return not_equal,
    }

    for i in (0..l_m).rev() {
        match m[i].cmp(&n[i]) {
            Ordering::Equal => (),
            not_equal => return not_equal
        }
    }
    Ordering::Equal
}

// Since we store little-endian, comparison needs to start at the last
// digit, instead of at the first as the derived / default implementation would.
impl<const D: usize, const E: usize> Ord for Unsigned<D, E> {
    fn cmp(&self, other: &Self) -> Ordering {
        generic_cmp_unsigned(self, other)
    }
}

// impl<T, const L: usize> PartialOrd<T> for Unsigned<L>
// where
//     T: AsNormalizedLittleEndianWords
// {
//     /// This is *little endian* ordering, as opposed to the default
//     /// ordering on arrays and slices!
//     fn partial_cmp(&self, other: &T) -> Option<Ordering> {
//         Some(generic_cmp_unsigned(self, other))
//     }
// }

impl<T, const D: usize, const E: usize> PartialOrd<T> for Unsigned<D, E>
where
    T: Number,
{
    /// This is *little endian* ordering, as opposed to the default
    /// ordering on arrays and slices!
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        Some(generic_cmp_unsigned(self, other))
    }
}

impl<T, const D: usize, const E: usize, const L: usize> PartialOrd<T> for Array<D, E, L>
where
    T: Number,
{
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        Some(generic_cmp_unsigned(self, other))
    }
}

// impl<T, const L: usize> PartialEq<T> for Unsigned<L>
// where
//     T: AsNormalizedLittleEndianWords
// {
//     fn eq(&self, other: &T) -> bool {
//         **self == **other
//     }
// }

impl<T, const D: usize, const E: usize> PartialEq<T> for Unsigned<D, E>
where
    T: Number,
{
    fn eq(&self, other: &T) -> bool {
        self.number() == other.number()
    }
}

impl<T, const D: usize, const E: usize, const L: usize> PartialEq<T> for Array<D, E, L>
where
    T: Number,
{
    fn eq(&self, other: &T) -> bool {
        self.number() == other.number()
    }
}

impl<T: Number, const D: usize, const E: usize> PartialEq<T> for Convenient<D, E> {
    fn eq(&self, other: &T) -> bool {
        self.number() == other.number()
    }
}

// impl<const D: usize, const E: usize> PartialEq<Odd<D, E>> for Unsigned<D, E> {
//     fn eq(&self, other: &Odd<D, E>) -> bool {
//         *self == **other//.words() == other.words()
//     }
// }

// impl<const L: usize> PartialEq<Unsigned<L>> for Odd<L> {
//     fn eq(&self, other: &Unsigned<L>) -> bool {
//         **self == *other
//     }
// }

// impl<const L: usize> PartialOrd<Odd<L>> for Unsigned<L> {
//     fn partial_cmp(&self, other: &Odd<L>) -> Option<core::cmp::Ordering> {
//         self.partial_cmp(&other.0)
//     }
// }

// impl<const L: usize> PartialOrd<Unsigned<L>> for Odd<L> {
//     fn partial_cmp(&self, other: &Unsigned<L>) -> Option<core::cmp::Ordering> {
//         self.0.partial_cmp(other)
//     }
// }

impl<const D: usize, const E: usize> Default for Unsigned<D, E> {
    fn default() -> Self {
        Self { lo: [0; D], hi: [0; E], cached_len: Some(0) }
    }
}

impl<const D: usize, const E: usize, const L: usize> Default for Array<D, E, L> {
    fn default() -> Self {
        Self { lo: [[0; D]; L], hi: [[0; E]; L], cached_len: Some(0) }
    }
}

impl<const D: usize, const E: usize> fmt::Debug for Unsigned<D, E> {
    /// TODO: Do we want debug output to be big-endian bytes (as currently implemented)?
    /// Or stick with internal representation?
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.to_be_bytes().as_be_bytes(), f)
    }
}

