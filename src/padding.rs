#![allow(unstable_name_collisions)]  // for Bits::BITS
//! Padding for RSA.
//!
//! Main reference is RFC 3447 (PKCS #1 v2.1), there is also RFC 8017 (v2.2).
//!
//! PKCS #1 v1.5 padding is of historical (and practical...) interest.
//! It is used both for encipherment + signatures.
//!
//! For encipherment, RSAES-OAEP is recommended.
//! This acronym means: RSA Encryption Scheme, with Optimal Asymmetric Encryption Padding.
//! The RFC defines a "label", which we restrict to empty in this implementation.
//!
//! For signatures, RSASSA-PSS is recommended.
//! This acronym means: RSA Signature Scheme with Appendix, with Probabilistc Signature Scheme
//! The RFC allows flexibility in a salt length, which we restrict to be the size of
//! the digest function's output in this implementation.
//!
//! The RFC allows a choice of "mask generating function" for both PSS + OAEP,
//! which we restrict to MGF1 in this implementation.
//!
//!
//!
//! TODO:
//!
//! - PKCS1-v1_5 for signatures does not use entropy; it sets PS = 0xFF bytes.
//! - generally, signature scheme paddings don't have to decode, just allow reconstructing
//!   the padded message to verify the right integer was signed.
//! - in the case of PSS, this means reconstructing the seed.
//!
//! Maybe rename to `armor.rs`?
//! https://news.ycombinator.com/item?id=3715393
//!
//!  "RSA padding" is one of the worst names in cryptography, because it isn't so much "padding" as it is "armor".
//!  If you don't pad in a very particular way, and check the padding scrupulously,
//!  you end up with multiple different vulnerabilities.
//!
//!
//!  TODO TODO TODO: For RSASSA PKCS1-v1_5, need to ASN.1-encode the hash :/

use core::marker::PhantomData;

use digest::{Digest, generic_array::typenum::Unsigned};
#[cfg(any(feature = "sha1", feature = "sha2"))]
use hex_literal::hex;
use rand_core::{CryptoRng, RngCore};

use crate::Long;
use crate::numbers::{BigEndianLong, Bits, NumberMut};

/// The spec has a few error cases.
///
/// Undecided whether to expose these at all.
pub enum Error {
    /// message too long to fit in number with required padding (encipherment case)
    MessageTooLong,
    /// RFC returns a different error for signature padding.
    /// This is because the message is hashed before signing, so it's a logic error
    /// to pick a integer (D) that's too small
    EncodingError,
    DecodingError,
    Inconsistent,
}

pub type Result<T> = core::result::Result<T, Error>;

/// Mask Generating Function 1
pub fn xor_mgf1<H: Digest>(hasher: &mut H, seed: &[u8], data: &mut [u8]) {
    hasher.reset();
    let mut c: u32 = 0;
    let h_len = H::OutputSize::to_usize();
    // "If either iterator returns None, next from the zipped iterator will return None"
    // So in the inner zipped loop, if the chunk is undersized, all is good
    for chunk in data.chunks_mut(h_len) {
        hasher.update(seed);
        hasher.update(c.to_be_bytes().as_ref());
        for (byte_to_mask, masking_byte) in chunk.iter_mut().zip(hasher.finalize_reset().iter()) {
            *byte_to_mask ^= *masking_byte;
        }
        c += 1;
    }
}

/// Helper type to convert between the big-endian bytes representation
/// in the spec and our internal little-endian digits representation.
pub struct Unpadded<const D: usize> {
    data: BigEndianLong<D>,
    offset: usize,
}

impl<const D: usize> Unpadded<D> {
    pub fn as_bytes(&self) -> &[u8] {
        &self.data[self.offset..]
        // &digit_slice_as_byte_slice(&self.data)[self.offset..]
    }
}

// impl<const D: usize> Deref for Unpadded<D> {
//     type Target = [u8];
//     fn deref(&self) -> &Self::Target {
//         self.as_bytes()
//     }
// }

// pub(crate) fn digit_slice_as_byte_slice(digits: &[Digit]) -> &[u8] {
//     unsafe { core::slice::from_raw_parts(
//         digits.as_ptr() as *const _ as *const _,
//         digits.len() * (Digit::BITS as usize / 8),
//     ) }
// }

// pub(crate) fn mut_digit_slice_as_mut_byte_slice(digits: &mut [Digit]) -> &mut [u8] {
//     unsafe { core::slice::from_raw_parts_mut(
//         digits.as_mut_ptr() as *mut _ as *mut _,
//         digits.len() * (Digit::BITS as usize / 8),
//     ) }
// }

/// Padding usable for encryption and decryption.
pub trait EncryptionPadding<const D: usize> {
    fn pad(msg: &[u8], rng: impl CryptoRng + RngCore)
        -> Result<Long<D>>;
    fn unpad(padded: &Long<D>) -> Result<Unpadded<D>>;
}

/// Padding usable for signatures and their verification.
///
/// PKCS1-v1_5 padding (for signatures) is deterministic, so ideally
/// we would have two of these types, one that requires and RNG in `pad`
/// and one that doesn't.
pub trait SignaturePadding<const D: usize> {
    fn pad(msg: &[u8], rng: impl CryptoRng + RngCore)
        -> Result<Long<D>>;
    /// Implementation note: Try to just regenerate the signature
    /// and compare, instead of parsing it.
    fn verify(msg: &[u8], padded: &Long<D>) -> Result<()>;
}

/// ## Probabilistic Signature Scheme.
///
/// TODO: This also want some ASN.1...
///
/// cf. https://github.com/google/wycheproof/blob/master/doc/rsa.md#rsa-pss
///
/// ```text
/// __________________________________________________________________
///
///                              +-----------+
///                              |     M     |
///                              +-----------+
///                                    |
///                                    V
///                                  Hash
///                                    |
///                                    V
///                      +--------+----------+----------+
///                 M' = |Padding1|  mHash   |   salt   |
///                      +--------+----------+----------+
///                                     |
///           +--------+----------+     V
///     DB =  |Padding2|   salt   |   Hash
///           +--------+----------+     |
///                     |               |
///                     V               |
///                    xor <--- MGF <---|
///                     |               |
///                     |               |
///                     V               V
///           +-------------------+----------+--+
///     EM =  |    maskedDB       |     H    |bc|
///           +-------------------+----------+--+
/// __________________________________________________________________
/// ```
#[derive(Clone, Default)]
pub struct Pss<H: Digest> { __: PhantomData<H> }

impl<H: Digest, const D: usize> SignaturePadding<D> for Pss<H> {
    fn pad(msg: &[u8], rng: impl CryptoRng + RngCore) -> Result<Long<D>> {
        // 2.
        let mut hasher = H::new();
        hasher.update(msg);
        let msg_hash = hasher.finalize_reset();

        // 3.
        let em_len = <Long<D> as Bits>::BITS / 8;
        let h_len = H::OutputSize::to_usize();
        if em_len < 2*h_len + 2 {
            return Err(Error::EncodingError);
        }

        // 4. + 5.
        let mut padded_buffer = BigEndianLong::<D>::default();
        let padded = &mut padded_buffer;
        debug_assert!(8 + 2*h_len <= em_len);

        padded[8..][..h_len].copy_from_slice(&msg_hash);

        let mut rng = rng;
        // need salt a second time later
        let mut salt = digest::generic_array::GenericArray::<u8, H::OutputSize>::default();
        rng.fill_bytes(&mut salt);
        padded[(8 + h_len)..][..h_len].copy_from_slice(&salt);
        let mprime = &padded[..(8 + 2*h_len)];

        // 6.
        hasher.update(mprime);
        let hash = hasher.finalize_reset();

        // 7.
        let db_len = em_len - h_len - 1;
        let ps_len = em_len - 2*h_len - 2;
        let (data_block, _hash_and_bc) = padded.split_at_mut(db_len);

        // 8.
        data_block[..ps_len].fill(0);
        data_block[ps_len] = 1;
        data_block[ps_len + 1..].copy_from_slice(&salt);

        // 9. + 10.
        xor_mgf1(&mut hasher, &hash, data_block);

        // 11.
        // skip?!

        // 12.
        padded[db_len..][..h_len].copy_from_slice(&hash);
        padded[em_len - 1] = 0xbc;

        // 13.
        Ok(Long::from_bytes(padded))
    }

    fn verify(msg: &[u8], padded: &Long<D>) -> Result<()> {
        // The main purpose of this exercise is to extract the salt
        // that was used during signing.

        let mut unpadded = Unpadded { data: padded.to_bytes(), offset: 0 };

        // 2.
        let mut hasher = H::new();
        hasher.update(msg);
        let msg_hash = hasher.finalize_reset();

        // 3.
        let em_len = <Long<D> as Bits>::BITS / 8;
        let h_len = H::OutputSize::to_usize();
        if em_len < 2*h_len + 2 {
            return Err(Error::Inconsistent);
        }

        // 4.
        let data_as_bytes: &mut [u8] = &mut unpadded.data;
        if data_as_bytes[em_len - 1] != 0xbc {
            return Err(Error::Inconsistent);
        }

        // 5.
        // still masked at this point
        let (data_block, remainder) = data_as_bytes.split_at_mut(em_len - h_len - 1);
        // let hash = &remainder[..h_len];
        let hash = digest::generic_array::GenericArray::<u8, H::OutputSize>::clone_from_slice(&remainder[..h_len]);

        // 6.
        // again, skip?!

        // 7. + 8.
        xor_mgf1(&mut hasher, &hash, data_block);

        // 9.
        // again, skip?!

        // 10.
        let (padding_string, one_and_salt) = data_block.split_at(em_len - 2*h_len - 2);
        // if !data_block[..em_len - 2*h_len - 2].iter().all(|&x| x == 0) {
        if !padding_string.iter().all(|&x| x == 0) {
            return Err(Error::Inconsistent);
        }
        if one_and_salt[0] != 1 {
            return Err(Error::Inconsistent);
        }

        // 11.
        let salt = digest::generic_array::GenericArray::<u8, H::OutputSize>::clone_from_slice(&one_and_salt[1..]);
        // let salt = &one_and_salt[1..];
        // debug_assert_eq!(salt.len(), h_len);

        // 12. reconstruct M'
        let mprime = &mut data_as_bytes[..8 + 2*h_len];
        mprime[..8].fill(0);
        mprime[8..][..h_len].copy_from_slice(&msg_hash);
        mprime[8 + h_len..].copy_from_slice(&salt);

        hasher.update(mprime);
        if hash != hasher.finalize_reset() {
            return Err(Error::Inconsistent);
        }

        Ok(())
    }
}

/// ## Optimal Asymmetric Encryption Padding.
///
/// data block DB = pHash || PS || 01 || M,
/// where padding string PS is em_len - msg.len() - 2*h_len - 1 zeros
///
/// then encoded message EM = masked seed || masked DB,
/// where first the random seed (of length hash::output) masks the DB,
/// and then the DB masks the seed
#[derive(Default)]
pub struct Oaep<H: Digest> { __: PhantomData<H> }

impl<H: Digest, const D: usize> EncryptionPadding<D> for Oaep<H> {
    fn pad(msg: &[u8], rng: impl CryptoRng + RngCore) -> Result<Long<D>> {
        // 1. TODO: message not too longer for hash function

        // 2. check message not too long
        let em_len = <Long<D> as Bits>::BITS / 8;
        let h_len = H::OutputSize::to_usize();
        if msg.len() + 2*h_len + 2 > em_len {
            return Err(Error::MessageTooLong);
        }

        // 3. construct datablock
        let mut padded_buffer = BigEndianLong::<D>::default();
        let padded = &mut padded_buffer[1..];

        let (seed, data_block) = padded.split_at_mut(h_len);

        let mut hasher = H::new();
        data_block[..h_len].copy_from_slice(&hasher.finalize_reset());

        let back_msg_and_one = data_block.len() - msg.len() - 1;
        let after_padding = &mut data_block[back_msg_and_one..];
        after_padding[0] = 0x1;
        after_padding[1..].copy_from_slice(msg);

        // 6.
        let mut rng = rng;
        rng.fill_bytes(seed);

        // 7. + 8. calculate maskedDB
        // hasher.reset();
        xor_mgf1(&mut hasher, seed, data_block);

        // 9. + 10. calculate maskedSeed
        // hasher.reset();
        xor_mgf1(&mut hasher, data_block, seed);

        Ok(Long::from_bytes(padded))
    }

    fn unpad(padded: &Long<D>) -> Result<Unpadded<D>> {
        let mut unpadded = Unpadded { data: padded.to_bytes(), offset: 0 };

        let em_len = <Long<D> as Bits>::BITS / 8;
        let h_len = H::OutputSize::to_usize();

        // 2.
        if em_len < 2 * h_len + 2 {
            return Err(Error::DecodingError);
        }

        // 3.
        let data_as_bytes: &mut [u8] = &mut unpadded.data;

        if data_as_bytes[0] != 0 {
            return Err(Error::DecodingError);
        }
        let data_as_bytes = &mut data_as_bytes[1..];

        // still masked at this point
        let (seed, data_block) = data_as_bytes.split_at_mut(h_len);

        // 4. + 5.
        let mut hasher = H::new();
        xor_mgf1(&mut hasher, data_block, seed);

        // 6. + 7.
        xor_mgf1(&mut hasher, seed, data_block);

        // 8. + 10.
        // assert_eq!(&data_block[..h_len], hasher.finalize().as_ref());
        if &data_block[..h_len] != hasher.finalize().as_ref() {
            return Err(Error::DecodingError);
        }
        let remainder = &mut data_block[h_len..];

        // 9.
        let ps_len = remainder.iter().enumerate()
            .find(|(_, digit)| **digit != 0)
            .map(|(i, _)| i)
            .ok_or(Error::DecodingError)?;

        if remainder[ps_len] != 1 {
            return Err(Error::DecodingError);
        }

        unpadded.offset = 2*h_len + ps_len + 2;

        Ok(unpadded)
    }
}

///  ## PKCS #1 v1.5 padding.
///
///  Defined in RFC 2313 (= PKCS #1 v1.5), see also
///  RFC 2437 (v2.0) and RFC 3447 (v2.1)
///
///  EM = 02 || PS || 00 || M, for encryption
///  EM = 00 || 01 || PS || 00 || M, for signatures
///
///  "encoded message", where the padding string PS is at least 8 bytes,
///  all non-zeros, and fills out the block.
#[derive(Default)]
pub struct Pkcs1<H: Digest> { __: PhantomData<H> }

#[repr(u8)]
enum Pkcs1Mode {
    Signing = 0x1,
    Encryption = 0x2,
}

// Called by encryption with a non-zero random filler,
// by signing with a constant 0xFF filler.
fn pkcs1_v1_5_pad<const D: usize>(
    der_prefix: &[u8],
    msg: &[u8],
    mode: Pkcs1Mode,
    filler: impl FnMut(&mut u8),
) -> Result<Long<D>> {
    // debug_assert!(D > 8);

    let em_len = Long::<D>::BITS / 8;

    let msg_len = der_prefix.len() + msg.len();
    if msg_len + 11 > em_len {
        return Err(Error::MessageTooLong);
    }

    let mut buffer = BigEndianLong::<D>::default();
    let all_bytes: &mut [u8] = &mut buffer;
    all_bytes[1] = mode as u8;

    let (padding_string, payload) = all_bytes.split_at_mut(em_len - msg_len - 1);
    let padding_string = &mut padding_string[2..];
    let payload = &mut payload[1..];

    padding_string.iter_mut().for_each(filler);
    payload[..der_prefix.len()].copy_from_slice(der_prefix);
    payload[der_prefix.len()..].copy_from_slice(msg);


    // // https://tools.ietf.org/html/rfc2313#section-8.1
    // as_bytes[..em_prefix.len()].copy_from_slice(em_prefix);
    // let padding_string_len = em_len - msg_len - 2 - em_prefix.len();
    // as_bytes[em_prefix.len()..][..padding_string_len].iter_mut().for_each(filler);

    // as_bytes[em_len - msg_len..][..msg_prefix.len()].copy_from_slice(msg_prefix);
    // as_bytes[em_len - msg_len + msg_prefix.len()..].copy_from_slice(msg);

    Ok(Long::from_bytes(all_bytes))
}

impl<H: Digest, const D: usize> EncryptionPadding<D> for Pkcs1<H> {
    fn pad(
        msg: &[u8],
        rng: impl CryptoRng + RngCore,
    ) -> Result<Long<D>> {
        let mut rng = rng;
        pkcs1_v1_5_pad(&[], msg, Pkcs1Mode::Encryption, |byte: &mut u8| {
            let mut trial = [0u8; 1];
            loop {
                rng.fill_bytes(&mut trial);
                if trial[0] != 0 {
                    *byte = trial[0];
                    break;
                }
            }
        })
    }

    fn unpad(padded: &Long<D>) -> Result<Unpadded<D>> {
        Self::unpad_mode(padded, Pkcs1Mode::Encryption)
    }
}

impl<H: Digest> Pkcs1<H> {
    fn unpad_mode<const D: usize>(padded: &Long<D>, mode: Pkcs1Mode) -> Result<Unpadded<D>> {
        // panic!("paddy: {:?}", padded);
        let mut unpadded = Unpadded { data: padded.to_bytes(), offset: 0 };

        let data: &mut [u8] = &mut unpadded.data;
        // panic!("paddy: {:?}", data_as_bytes);

        if data.len() < 10 {
            return Err(Error::DecodingError);
        }

        if data[0] != 0 || data[1] != mode as u8 {
            // panic!("voila: {:?}", data);
            return Err(Error::DecodingError);
        }

        const PADDING_START: usize = 2;
        unpadded.offset = data[PADDING_START..].iter().enumerate()
            .find(|(_, byte)| **byte == 0)
            .map(|(i, _)| i + 1 + PADDING_START)
            .ok_or(Error::DecodingError)?;
        Ok(unpadded)
    }

}

#[cfg(feature = "sha1")]
pub const SHA1_PREFIX: &[u8] = &hex!("30 21 30 09 06 05 2b 0e 03 02 1a 05 00 04 14");

#[cfg(feature = "sha2")]
pub const SHA256_PREFIX: &[u8] = &hex!("30 31 30 0d 06 09 60 86 48 01 65 03 04 02 01 05 00 04 20");
#[cfg(feature = "sha2")]
pub const SHA384_PREFIX: &[u8] = &hex!("30 41 30 0d 06 09 60 86 48 01 65 03 04 02 02 05 00 04 30");
#[cfg(feature = "sha2")]
pub const SHA512_PREFIX: &[u8] = &hex!("30 51 30 0d 06 09 60 86 48 01 65 03 04 02 03 05 00 04 40");

/// ASN.1 prefixes for RSASSA-PKCS1-v1_5.
///
/// RSASSA-PKCS1-v1_5 likes to wrap its hashed message in
/// an ASN.1 `DigestInfo` structure. This could have been done
/// with just a byte but... Instead of including a DER-writer or
/// even parser, we hardcode the requisite prefixes, and implement
/// this trait for RustCrypto digest implementations. To use a
/// different digest implementation, implement this trait for that
/// implementation, using the public constants.
pub trait Asn1Digest: Digest {
    const ASN1_PREFIX: &'static [u8];
}

#[cfg(feature = "sha1")]
impl Asn1Digest for sha1::Sha1 {
    const ASN1_PREFIX: &'static [u8] = SHA1_PREFIX;
}

#[cfg(feature = "sha2")]
impl Asn1Digest for sha2::Sha256 {
    const ASN1_PREFIX: &'static [u8] = SHA256_PREFIX;
}

#[cfg(feature = "sha2")]
impl Asn1Digest for sha2::Sha384 {
    const ASN1_PREFIX: &'static [u8] = SHA384_PREFIX;
}

#[cfg(feature = "sha2")]
impl Asn1Digest for sha2::Sha512 {
    const ASN1_PREFIX: &'static [u8] = SHA512_PREFIX;
}

impl<H: Asn1Digest, const D: usize> SignaturePadding<D> for Pkcs1<H> {
    fn pad(
        msg: &[u8],
        _rng: impl CryptoRng + RngCore,
    ) -> Result<Long<D>> {
        let mut hasher = H::new();
        hasher.update(msg);
        let hashed_msg = hasher.finalize();
        pkcs1_v1_5_pad(H::ASN1_PREFIX, &hashed_msg, Pkcs1Mode::Signing, |byte: &mut u8| *byte = 0xFF)
    }

    fn verify(msg: &[u8], verifier: &Long<D>) -> Result<()> {
        // No Bleichenbacher06 for us!
        // https://tools.ietf.org/html/rfc8017#section-8.2.2
        let mut hasher = H::new();
        hasher.update(msg);
        let hashed_msg = hasher.finalize();

        let padded_hashed_msg: Long<D> = pkcs1_v1_5_pad(
            H::ASN1_PREFIX, &hashed_msg, Pkcs1Mode::Signing, |byte: &mut u8| *byte = 0xFF)?;

        (*verifier == padded_hashed_msg)
            .then(|| ())
            .ok_or(Error::Inconsistent)
    }

}

#[cfg(test)]
mod test {
    // use super::*;

    // TODO: obviously!
    //
    // Test vectors from NIST: https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/digital-signatures#rsavs
    // Test vectors from Google: https://github.com/google/wycheproof/tree/master/testvectors

    #[test]
    fn short_pkcs1_v1_5() {
        let _msg = "hello, world!";

        // let encoded: Long::<D> = pkcs1v1_5(msg, rng);
    }

    #[test]
    fn hash_of_empty() {
        // some kind of test that
        // SHA256(<empty>) = 30 31 30 0d 06 09 60 86 48 01 65 03 04 02 01 05 00 04 20
    }
}
