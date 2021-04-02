use core::{cmp::Ordering, convert::TryFrom, ops::{Deref, DerefMut, Index, IndexMut}};

use super::{Digit, NonZeroOdd, NormalizedLittleEndian, NormalizedLittleEndianMut, Prime, Product, Unsigned, UnsignedCarry};
use crate::{Error, Result};


impl Deref for NormalizedLittleEndian<'_> {
    type Target = [u32];
    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl Deref for NormalizedLittleEndianMut<'_> {
    type Target = [u32];
    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl DerefMut for NormalizedLittleEndianMut<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

// impl<const L: usize> Deref for Unsigned<L> {
//     type Target = [u32];
//     fn deref(&self) -> &Self::Target {
//         &self.0
//     }
// }

// impl<const L: usize> DerefMut for Unsigned<L> {
//     fn deref_mut(&mut self) -> &mut Self::Target {
//         &mut self.0
//     }
// }

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

// impl<const L: usize> core::convert::AsRef<Unsigned<L>> for NonZeroOdd<L> {
//     fn as_ref(&self) -> &Unsigned<L> {
//         &self.0
//     }
// }

// impl<const L: usize> core::convert::AsMut<Unsigned<L>> for NonZeroOdd<L> {
//     fn as_mut(&mut self) -> &mut Unsigned<L> {
//         &mut self.0
//     }
// }

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

// impl<const L: usize> core::convert::AsRef<NonZeroOdd<L>> for Prime<L> {
//     fn as_ref(&self) -> &NonZeroOdd<L> {
//         &self.0
//     }
// }

// impl<const L: usize> core::convert::AsMut<NonZeroOdd<L>> for Prime<L> {
//     fn as_mut(&mut self) -> &mut NonZeroOdd<L> {
//         &mut self.0
//     }
// }

impl<const L: usize> TryFrom<Unsigned<L>> for NonZeroOdd<L> {
    type Error = Error;
    fn try_from(unsigned: Unsigned<L>) -> Result<Self> {
        // non-zero
        if unsigned == Unsigned::zero() {
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

// Since we store little-endian, comparison needs to start at the last
// digit, instead of at the first as the derived / default implementation would.
impl<'a> Ord for NormalizedLittleEndian<'a> {
    /// This is *little endian* ordering, as opposed to the default
    /// ordering on arrays and slices!
    fn cmp(&self, other: &Self) -> Ordering {
        let l_self = self.len();
        let l_other = other.len();
        match l_self.cmp(&l_other) {
            Ordering::Equal => {}
            not_equal => return not_equal,
        }

        for i in (0..l_self).rev() {
            match self[i].cmp(&other[i]) {
                Ordering::Equal => (),
                not_equal => return not_equal
            }
        }
        Ordering::Equal
    }
}

impl PartialOrd for NormalizedLittleEndian<'_> {
    /// This is *little endian* ordering, as opposed to the default
    /// ordering on arrays and slices!
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// Since we store little-endian, comparison needs to start at the last
// limb, instead of at the first as the derived / default implementation would.
impl<const L: usize> PartialOrd for Unsigned<L> {
    /// This is *little endian* ordering, as opposed to the default
    /// ordering on arrays and slices!
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const L: usize> Ord for Unsigned<L> {
    /// This is *little endian* ordering, as opposed to the default
    /// ordering on arrays and slices!
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_le_words().cmp(&other.as_le_words())
    }
}

impl<const L: usize> PartialEq<NonZeroOdd<L>> for Unsigned<L> {
    fn eq(&self, other: &NonZeroOdd<L>) -> bool {
        *self == other.0
    }
}

impl<const L: usize> PartialEq<Unsigned<L>> for NonZeroOdd<L> {
    fn eq(&self, other: &Unsigned<L>) -> bool {
        self.0 == *other
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

// impl<const L: usize> AsRef<[u32]> for Unsigned<L> {
//     fn as_ref(&self) -> &[u32] {
//         &self.0
//     }
// }

// impl<const L: usize> AsMut<[u32]> for Unsigned<L> {
//     fn as_mut(&mut self) -> &mut [u32] {
//         &mut self.0
//     }
// }

impl<const L: usize> Index<usize> for Product<L> {
    type Output = Digit;
    fn index(&self, i: usize) -> &Self::Output {
        &self.as_le_words().0[i]
    }
}

impl<const L: usize> IndexMut<usize> for Product<L> {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        if i < L {
            &mut self.lo.0[i]
        } else {
            &mut self.hi.0[i - L]
        }
    }
}

impl<const L: usize> Index<usize> for UnsignedCarry<L> {
    type Output = Digit;
    fn index(&self, i: usize) -> &Self::Output {
        &self.as_le_words().0[i]
    }
}

impl<const L: usize> IndexMut<usize> for UnsignedCarry<L> {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        if i < L {
            &mut self.lo.0[i]
        } else if i == L {
            &mut self.carry
        } else {
            panic!("out of bounds");
        }
    }
}
