use crate::{Convenient, Odd, Prime, Short};
pub use crate::aliases::*;
pub use crate::key::{PrivateKey, Rsa, Rsa5c, Rsa1k};
pub use crate::numbers::NumberMut;

pub use hex_literal::hex;

// Examples here were generated using pyca/cryptography 3.4.6:
// cryptography.hazmat.primitives.asymmetric.rsa.generate_private_key(0x10001, <N bits>)

/// p = 100292567896662137431268955658963309646243393373296740296994110575772313854713
/// = 0xddbb94f11af83b2adf02e961bd5ad74aca27a8bd7ee8dd0cab998f987cd022f9
pub fn p256() -> Prime256 {
    Prime(Convenient(Odd(Short::from_bytes(&hex!("ddbb94f11af83b2adf02e961bd5ad74aca27a8bd7ee8dd0cab998f987cd022f9")))))
}

/// q = 92881035101327452495721684699134578528389025346126041237323965302769971181967
/// = 0xcd58cd8accf2db4c839d2553116bef81f0292b4e2d2b3f7df0e5dc8a0721398f
pub fn q256() -> Prime256 {
    Prime(Convenient(Odd(Short::from_bytes(&hex!("cd58cd8accf2db4c839d2553116bef81f0292b4e2d2b3f7df0e5dc8a0721398f")))))
}

// rsa5c-example.pem
// >>> from cryptography.hazmat.primitives import serialization
// >>> privkey = serialization.load_pem_private_key(open("rsa5c-example.pem", "rb").read(), password=None)

// pp = 0xf48922fe8e8cf7e238c32399aacd26d2467ec5510efb5113ad2bcc37e6fe2bed
pub fn pp256() -> Prime256 {
    Prime(Convenient(Odd(Short::from_bytes(&hex!("f48922fe8e8cf7e238c32399aacd26d2467ec5510efb5113ad2bcc37e6fe2bed")))))
}
// qq = 0xf146b14fe50dad906063caba3606e1157dee090be85c7cdb06022ea6dd306c63
pub fn qq256() -> Prime256 {
    Prime(Convenient(Odd(Short::from_bytes(&hex!("f146b14fe50dad906063caba3606e1157dee090be85c7cdb06022ea6dd306c63")))))
}

/// n512 = p256*q256
/// = 9315277519212142779151476376293622563023107584513130937761509198001155297478923849044657378490092399125800365538632936331104530278427184580913858523560471
/// = 0xb1dc20c7b4613d3ba806189f4755ee81b25c8a466af66649a901c23efda054d4bac18a9d6827494b657e9a1b791123bc5c5d5c9a4447330598cfc7fb6125fa17
pub fn n512() -> Short512 {
    Short512::from_bytes(&hex!(
        "b1dc20c7b4613d3ba806189f4755ee81b25c8a466af66649a901c23efda054d4bac18a9d6827494b657e9a1b791123bc5c5d5c9a4447330598cfc7fb6125fa17"))
}

pub fn rsa512() -> <Rsa5c as Rsa>::PrivateKey {
    let p = pp256();
    let q = qq256();
    let precomputed = (&p, &q).into();
    let public_key = (&p, &q).into();

    PrivateKey { p, q, precomputed, public_key }
}

/// Just another (convenient, prime) number
/// c = 0xc6629218173d87d4ce2b0c0338b699dec701c1bcff0be39f80bb02fe0a458147
pub fn c256() -> Short256 {
    Short::from_bytes(&hex!("c6629218173d87d4ce2b0c0338b699dec701c1bcff0be39f80bb02fe0a458147"))
}

/// Randomly generated 480-bit "message"
pub fn msg480() -> Short512 {
    Short::from_bytes(&hex!("6a7f5d4a4ddff708442d837f7dc6ddb098bd44fd68854b691677e7665f81c4e4492f4e4200abf1a7b889006f30bc2fdc3743c94a647f78fe15293367"))
}

pub fn p512() -> Prime512 {
    Prime(Convenient(Odd(Short::from_bytes(&hex!(
        "e2b5d8aa80414214685ca7581013614689200d2f6530389afcf7725ad5d5431d8feaefd5679a9414c3b041828f448332e597793dbdc3ee044988e83f2d1599d7")))))
}

pub fn q512() -> Prime512 {
    Prime(Convenient(Odd(Short::from_bytes(&hex!(
        "cf58cd3e0cbbde7540488f803e122acc5401ab10fe93882e9c49a21b4fd626ef322142ccb79eb8ba0de54d6f4b2fe1b0cd9f07d7653951b0db9384003ee0fd25")))))
}

/// A 1024-bit convenient prime.
pub fn p1024() -> Prime1024 {
    Prime(Convenient(Odd(Short::from_bytes(&hex!(
        "f6943831dadf848ff8f7f6e44f56c25448e4bf667fe5fbe65437c4e01c2c1380dcd32c314e0a5426d49ddcf02839bc6f29fef131dbde9e43066b56898db20e66c89d0fbb373311ca39c8df0a57cbab41338b7a0edae3dff5c58425b50aa8359b30b07176f04e2a44b9c3236bd5d1712759952dce2fc0f4bb4be659b236eef82d"
    )))))
}

/// A 1024-bit convenient prime.
pub fn q1024() -> Prime1024 {
    Prime(Convenient(Odd(Short::from_bytes(&hex!(
        "ec7fd9ac14acd39bace11a2b523d274d465d79e3b7e011cdec7adb94a94e124064894672148ab25279d605854c6dbf91f981330c9f76a7682eb9e5ea08ec4eb46084e9671bfb5db02a46742bf100de162def6ab0b2eea76ddf382eddff9be104fd8471fb2fed043bd6e3db4831b788b68e9f009c66f4ae02869d1e3cdd2c6361"
    )))))
}

/// The product `p1024 * q1024`.
pub fn n2048() -> Short2048 {
    Short::from_bytes(&hex!(
        "e3cbc8ff39a3b2e9c5a83ebd25bfc064ddf9ea686ff0f617e3f4108726085162e719d2c8f2058d1edef62edc9233ce281f501b480c462cec9d55c05396c0a8c7b1eced045a62737043effeeed08946296dbbe22d1142a533c7adc9a8e5e68fb74e9c33b5fbe0b71275e8d0a36e53419fa6e143872a64fcbd598d8a68ca3040a3a13bf502e17c6ec8241a5d2a60daf658ada18496111fcd5fa894650435efd153ec3be4d3f0f51511839226550089598efc8186d6b08d9b9b9855dd157cdf038ed1ee3c76f007e94fa70308b5e1c0c53a63b4b40712064891c1af1e05cd6e84354e4f6b5bfdf7a107b3bb87ba2d08781cab7bf0d7de75455cbdb615a2bb41700d"
    ))
}

pub struct CountingRng(pub(crate) u64);

impl rand_core::RngCore for CountingRng {
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    fn next_u64(&mut self) -> u64 {
        self.0 += 1;
        self.0
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        rand_core::impls::fill_bytes_via_next(self, dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        Ok(self.fill_bytes(dest))
    }
}

// yeah right hahaha
impl rand_core::CryptoRng for CountingRng {}

#[cfg(test)]
mod test {
    use crate::numbers::NumberMut;
    use super::*;

    #[cfg(feature = "q-inverse")]
    #[test]
    fn q_inverse() {
        let key = rsa512();

        let p = &key.p;
        let q = &key.q;
        let q_inv = &key.precomputed.q_inv;

        assert_eq!(
            (&q.as_odd().modulo(p) * &q_inv.modulo(p)).canonical_lift(),
            Short256::one(),
        );
    }
}
