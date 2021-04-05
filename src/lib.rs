#![cfg_attr(not(test), no_std)]
mod arithmetic;
pub use arithmetic::{Modular, Montgomery, ShortModular, ShortMontgomery};
mod error;
pub use error::{Error, Result};
mod key;
pub use key::{PrivateKey, PublicKey};
// pub use key::{Rsa, Rsa2k, Rsa3k, Rsa4k};
pub mod numbers;
pub use numbers::{
    FromSlice, Number ,NumberMut,
    Digit, DoubleDigit, Limb, SignedDoubleDigit,
    Array, Odd, Prime, Product, Short, Unsigned,
};

// mod primitive;

/// The fourth Fermat prime, $2^{16} + 1$.
///
/// This library only implements RSA keys with public exponent `e = 65537 = 0x10001 = u16::MAX + 2`.
///
/// An example recommendation to do so is RFC 4871: <https://www.ietf.org/rfc/rfc4871.txt>,
/// more generally, there seems no need to have too many knobs to turn.
///
pub const F4: u32 = 0x10001;

// /// F4 (aka E, aka e, aka the fourth Fermat prime) as Unsigned of length 1.
// pub const UE: Unsigned<1> = Unsigned([E]);
