//! Type aliases by bit-size, independent of architecture/features.

use crate::{Long, Short, ShortPrime};
pub use aliases::*;

// 32-bit
#[cfg(any(target_pointer_width = "32", feature = "u32"))]
mod aliases {
    use super::*;

    pub type Prime256 = ShortPrime<8>;
    pub type Prime512 = ShortPrime<16>;
    pub type Prime1024 = ShortPrime<32>;
    pub type Prime1536 = ShortPrime<48>;
    pub type Prime2048 = ShortPrime<64>;

    pub type Short32 = Short<1>;
    pub type Short64 = Short<2>;
    pub type Short128 = Short<4>;
    pub type Short256 = Short<8>;
    pub type Short512 = Short<16>;
    pub type Short1024 = Short<32>;
    pub type Short1536 = Short<48>;
    pub type Short2048 = Short<64>;
    pub type Short3072 = Short<96>;
    pub type Short4096 = Short<128>;

    pub type Long64 = Long<1>;
    pub type Long128 = Long<2>;
    pub type Long256 = Long<4>;
    pub type Long512 = Long<8>;
    pub type Long1024 = Long<16>;
    pub type Long1536 = Long<24>;
    pub type Long2048 = Long<32>;
    pub type Long3072 = Long<48>;
    pub type Long4096 = Long<64>;
}

// 64-bit
#[cfg(all(target_pointer_width = "64", not(feature = "u32")))]
mod aliases {
    use super::*;

    pub type Prime256 = ShortPrime<4>;
    pub type Prime512 = ShortPrime<8>;
    pub type Prime1024 = ShortPrime<16>;
    pub type Prime1536 = ShortPrime<24>;
    pub type Prime2048 = ShortPrime<32>;

    pub type Short64 = Short<1>;
    pub type Short128 = Short<2>;
    pub type Short256 = Short<4>;
    pub type Short512 = Short<8>;
    pub type Short1024 = Short<16>;
    pub type Short1536 = Short<24>;
    pub type Short2048 = Short<32>;
    pub type Short3072 = Short<48>;
    pub type Short4096 = Short<64>;

    pub type Long128 = Long<1>;
    pub type Long256 = Long<2>;
    pub type Long512 = Long<4>;
    pub type Long1024 = Long<8>;
    pub type Long1536 = Long<12>;
    pub type Long2048 = Long<16>;
    pub type Long3072 = Long<24>;
    pub type Long4096 = Long<32>;

}


