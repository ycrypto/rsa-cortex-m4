use crate::{Convenient, Odd, Prime, Short};
pub use crate::aliases::*;
pub use crate::numbers::NumberMut;

use hex_literal::hex;

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

/// Just another (convenient, prime) number
/// c = 0xc6629218173d87d4ce2b0c0338b699dec701c1bcff0be39f80bb02fe0a458147
pub fn c256() -> Short256 {
    Short::from_bytes(&hex!("c6629218173d87d4ce2b0c0338b699dec701c1bcff0be39f80bb02fe0a458147"))
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