//! The RSA primitive.

use crate::{Modular, Result, Unsigned};
use rand_core::{CryptoRng, RngCore};

pub(crate) trait PublicRsaPrimitive<const L: usize> {
    // or "public operation"
    // or "public permutation"
    fn rsa_primitive(
        &self,
        plaintext: &[u8],
        pad_size: usize,
    ) -> Result<[u32; L]>;
}

pub(crate) trait PrivateRsaPrimitive<const L: usize> {
    // or "private operation"
    // or "private permutation"
    fn rsa_primitive<R: CryptoRng + RngCore>(
        &self,
        rng: Option<&mut R>,
        ciphertext: &[u8],
        pad_size: usize,
    ) -> Result<[u32; L]>;
}

///// Since all operations are hopelessly non-constant time, everything
///// sensitive is "blinded" using the RNG.
/////
//fn decrypt<const L: usize>(
//    rng: impl CryptoRng + RngCore,
//    key: PrivateKey,
//    ciphertext: Modular<'_, L>,
//) -> Result<Unsigned<L>>
//{
//    // ciphertext.modulo(n).power(key.d)
//    //
//    let p = &key.p;
//    let q = &key.q;

//    let e: Unsigned<L> = crate::E.into();

//    // while `e` stands for the "encryption exponent",
//    // the various `d`'s are the "decryption exponents."
//    let dp = e.modulo(p).inverse();
//    let dq = e.modulo(q).inverse();

//    let mp = ciphertext.lift().modulo(p).power(&dp);
//    let mq = ciphertext.lift().modulo(q).power(&dq);

//    ((mp - mq.lift().modulo(p)) * (&q.modulo(n).inverse()) + mq).lift();

//    todo!();
//}
