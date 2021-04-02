#![cfg_attr(not(test), no_std)]
mod arithmetic;
pub use arithmetic::{Digit, Modular, NonZeroOdd, Prime, Product, Unsigned};
mod error;
pub use error::{Error, Result};
mod key;
pub use key::{Rsa, Rsa2k, Rsa3k, Rsa4k};

// mod primitive;

/// This library only implements RSA keys with public exponent `e = 65537`.
///
/// An example recommendation is RFC 4871:
/// https://www.ietf.org/rfc/rfc4871.txt
pub const E: u32 = 0x10001;

/// F4 (aka E, aka e, aka the fourth Fermat prime) as Unsigned of length 1.
pub const UE: Unsigned<1> = Unsigned([E]);
