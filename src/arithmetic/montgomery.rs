use ref_cast::RefCast;
use subtle::{ConditionallySelectable, ConstantTimeEq};

use crate::{Convenient, Digit, DoubleDigit, Modular, Montgomery, SignedDoubleDigit};
use crate::numbers::{Array, Bits, Number, Unsigned};
use super::Wrapping;

pub(crate) fn q0_for_p<const D: usize, const E: usize>(p: &Convenient<D, E>) -> Digit {
    let p0 = p[0];
    digit_minus_inverse(p0)
}

#[inline]
fn mod_two(x: Digit, i: usize) -> Digit {
    x & ((1 << i) - 1)
}

/// Inverse of odd number modulo power of two: $x^{-1}\text{ mod }b$
///
/// This has $\mathcal{O}(n)$ loops in `Digit::BITS`.
///
/// Source: `Modular-Inverse(x,b)` from
/// [A Cryptographic Library for the Motorola DSP56000 (1990)][dusse-kaliski]
///
/// [dusse-kaliski]: https://api.semanticscholar.org/CorpusID:7044569
#[allow(dead_code)]
fn x_inverse_digit_dusse_kaliski(x: Digit) -> Digit {
    debug_assert_ne!(x & 1,  0);

    let mut y: Digit = 1;
    for i in 2..Digit::BITS {
        let two_to_the_i_minus_1 = 1 << (i - 1);
        if mod_two(x.wrapping_mul(y), i) >= two_to_the_i_minus_1 {
            y = y.wrapping_add(two_to_the_i_minus_1);
        }
    }

    let two_to_the_b_minus_1 = 1 << (Digit::BITS - 1);
    if x.wrapping_mul(y) >= two_to_the_b_minus_1 {
        y = y.wrapping_add(two_to_the_b_minus_1)
    }
    y
}

/// Inverse of odd number modulo power of two: $e^{-1}\text{ mod }2^{|f|}$
///
/// This has $\mathcal{O}(\log n)$ loops in `Digit::BITS`, much more efficient
/// than the Dusse-Kaliski method: 5 iterations for u32, 6 iterations for u64.
///
/// This method also applies to inversion in `Unsigned` (in the wrapping
/// interpretation of `Mul` that we use).
///
/// Source: Fig. 1 from
/// [GCD-Free Algorithms for Computing Modular Inverses (2003)][joy-paillier]
///
/// Note that this source is highly confusing! What they mean to say
/// is to iterate $y \leftarrow y(2 - ey)$ in $\mathbb{Z}/2^{|f|}$,
/// where the output is an inverse of $e$ modulo $2^{2i}$.
///
/// In other words, the $\text{mod }2^i$ is a typo, and should be $\text{mod }2^{|f|}$.
///
/// Cf. [Crypto StackExchange][cse].
///
/// [joy-paillier]: https://api.semanticscholar.org/CorpusID:17736455
/// [cse]: https://crypto.stackexchange.com/a/47496
fn e_inverse_digit_joye_paillier(e: Digit) -> Digit {
    debug_assert_ne!(e & 1,  0);

    // log_2(32) = 5, log_2(64) = 6.
    #[allow(non_snake_case)]
    let T = Digit::BITS.trailing_zeros();
    let mut y: Digit = 1;
    let two: Digit = 2;

    for _ in 1..=T {
        y = y.wrapping_mul(two.wrapping_sub(e.wrapping_mul(y)));// % (1 << i);
    }
    y
}

/// $Q_0 = -P_0^{-1}\text{(mod }2^{w}\text{)}$
#[allow(dead_code)]
fn digit_minus_inverse(p0: Digit) -> Digit {
    e_inverse_digit_joye_paillier(p0).wrapping_neg()
}

#[allow(dead_code)]
fn mac(t: Digit, a: Digit, b: Digit, c: &mut Digit) -> Digit {
    // use crate::DoubleDigit;
    let total: DoubleDigit = (t as DoubleDigit) + ((a as DoubleDigit)*(b as DoubleDigit)) + (*c as DoubleDigit);
    *c = (total >> Digit::BITS) as Digit;
    total as Digit
}

// R mod p
#[inline]
#[allow(non_snake_case)]
fn R_mod_p<const D: usize, const E: usize>(n: &Convenient<D, E>) -> Unsigned<D, E> {
    // by "convenience", R = R - p (mod p) = -p (mod R)
    (-Wrapping::ref_cast(n.as_ref())).0
}

// R*R mod p
#[inline]
#[allow(non_snake_case)]
fn R2_mod_p<const D: usize, const E: usize>(n: &Convenient<D, E>) -> Unsigned<D, E> {
    let R = R_mod_p(n);
    &(&R * &R) % n.as_ref()
}

// Essentially: MM(A, R*R) = A*R*R*R^{-1} = AR =: A'
//
// This has an expensive step of multiplying [R]_p and then reducing mod p.
#[allow(non_snake_case)]
pub fn to_montgomery<'n, const D: usize, const E: usize>(modular: &Modular<'n, D, E>) -> Montgomery<'n, D, E> {

    let R2 = R2_mod_p(modular.n);//&(&R * &R) % modular.n.as_ref();

    debug_assert!(!R2.is_zero());

    let q0 = q0_for_p(modular.n);

    Montgomery {
        y: cios_montgomery_product(&modular.x, &R2, modular.n, q0),
        n: modular.n,
    }
}

// Essentially: MM(A', 1) = A'*1*R^{-1} = A*R*R^{-1} = A
pub fn to_modular<'n, const D: usize, const E: usize>(montgomery: &Montgomery<'n, D, E>) -> Modular<'n, D, E> {
    let q0 = q0_for_p(montgomery.n);
    Modular {
        x: cios_montgomery_product(&montgomery.y, &Unsigned::from(1), montgomery.n, q0),
        n: montgomery.n,
    }
}

// the operation (C, S) := t + a*b + C
// is: s = mac(t, a, b, &mut c)

// /// Following [Incomplete Reduction in Modular Arithmetic (Yanik/Savaş/Koç, 2012)][ysk12].
// /// [ysk12]: https://api.semanticscholar.org/CorpusID:17543811
// #[allow(non_snake_case)]
// pub(crate) fn montgomery_multiply<const D: usize, const E: usize>(
//     A: &Unsigned<D, E>,
//     B: &Unsigned<D, E>,
//     P: &Convenient<D, E>,
//     q0: Digit,

// ) -> Unsigned<D, E> {

//     // step 1 + 2
//     let mut T = Unsigned::<D, E>::zero();

//     // steps 3-7: partial product T of length D + 1
//     let mut c: Digit = 0;

//     let s = D + E;

//     for i in 0..s  {
//         c = 0;
//         // for j in 0..s {
//         //     T[j] = mac(T[j], A[i], B[j], &mut c);
//         // }
//         // let Ts = c;

//         // This doesn't seem to work / coincide at all.
//         let Ts = super::multiply::add_product_by_digit_into(&mut T, &B, A[i]);

//         // steps 8-12: reduce T modulo p, to length D
//         let M = T[0].wrapping_mul(q0);
//         // let M = ((T[0] as DoubleDigit) * (q0 as DoubleDigit)) as Digit;
//         assert_eq!(M.wrapping_mul(P[0]), T[0].wrapping_neg());

//         // step 9
//         let X = (T[0] as DoubleDigit) + (M as DoubleDigit)*(P[0] as DoubleDigit);
//         debug_assert_eq!(X as Digit, 0);
//         c = (X >> Digit::BITS) as Digit;

//         // c = 0;  // the `as Digit` part (return value) is dropped anyway
//         // mac(T[0], M, P[0], &mut c);

//         for j in 1..s {
//             T[j - 1] = mac(T[j], M, P[j], &mut c);
//         }

//         T[s - 1] = mac(Ts, 0, 0, &mut c);

//         // let T = (T + M*P) >> 1;
//     }

//     // return Short::from_slice(&T[..D]);

//     // step 13: can exceed R - 1 by at most p
//     // if c == 0 {
//         return T;
//     // }

//     // steps 14-16: print T to range $[0, R - 1]$.
//     // T -= P;
//     T.wrapping_sub_assign(P.as_ref());
//     // let mut b: Digit = 0;
//     // for j in 0..D {
//     //     let outcome = (T[j] as DoubleDigit).wrapping_sub(P[j] as DoubleDigit).wrapping_sub(b as DoubleDigit);
//     //     T[j] = outcome as Digit;
//     //     b = (outcome >> Digit::BITS) as Digit;
//     // }

//     return T;
// }


#[allow(non_snake_case)]
#[allow(dead_code)]
fn ADD(target: &mut [Digit], top_word: &mut Digit, C: Digit) {
    *top_word += super::add::add_assign_carry(target, &[C]);
}

#[allow(non_snake_case)]
pub(crate) fn conditionally_subtract_n<const D: usize, const E: usize>(
    u: &Unsigned<D, E>,
    us: Digit,
    n: &Convenient<D, E>
) -> Unsigned<D, E> {

    let s = D + E;

    let mut B: SignedDoubleDigit = 0;
    let mut t = Unsigned::<D, E>::zero();
    for i in 0..=(s-1) {
        t[i] = super::subtract::sbb(u[i], n[i], &mut B)
    }
    let _ts = super::subtract::sbb(us, 0, &mut B);

    Unsigned::conditional_select(&u, &t, B.ct_eq(&0))
}


#[allow(non_snake_case)]
#[allow(dead_code)]
/// The Separated Operand Scanning (SOS) method
pub(crate) fn sos_montgomery_product<const D: usize, const E: usize>(
    a: &Unsigned<D, E>,
    b: &Unsigned<D, E>,
    n: &Convenient<D, E>,
    n_prime_0: Digit,
) -> Unsigned<D, E> {

    let s = D + E;

    // 1. compute product a·b
    let mut t = Array::<D, E, 2>::zero();
    for i in 0..=(s-1) {
        let mut C: Digit = 0;
        for j in 0..=(s-1) {
            t[i+j] = mac(t[i+j], a[j], b[i], &mut C);
        }
        t[i + s] = C;
    }

    // 2. compute u := (t + m·n)/r where m := t·n' mod r
    //
    // using n'0 = n' as Digit instead of n'

    let mut t2s: Digit = 0;
    for i in 0..=(s-1) {
        let mut C: Digit = 0;
        let m = t[i].wrapping_mul(n_prime_0);
        for j in 0..=(s-1) {
            t[i+j] = mac(t[i+j], m, n[j], &mut C);
        }
        ADD(&mut t[i + s..], &mut t2s, C);
    }
    // if T2s != 0 { panic!();}

    // 3. u in s + 1 words
    let u = Unsigned::<D, E>::from_slice(&t[s..]);
    let us = t2s;

    // 4. reduce u if necessary
    conditionally_subtract_n(&u, us, n)
    // let mut B: SignedDoubleDigit = 0;
    // let mut t = Unsigned::<D, E>::zero();
    // for i in 0..=(s-1) {
    //     t[i] = super::subtract::sbb(u[i], n[i], &mut B)
    // }
    // let _ts = super::subtract::sbb(us, 0, &mut B);

    // Unsigned::conditional_select(&u, &t, B.ct_eq(&0))
}

#[allow(non_snake_case)]
/// The Coarsely Integrated Operand Scanning (CIOS) method
pub(crate) fn cios_montgomery_product<const D: usize, const E: usize>(
    a: &Unsigned<D, E>,
    b: &Unsigned<D, E>,
    n: &Convenient<D, E>,
    n_prime_0: Digit,
) -> Unsigned<D, E> {

    let s = D + E;
    let mut t = Unsigned::<D, E>::zero();
    let mut ts: Digit = 0;
    let mut ts1: Digit;

    for i in 0..=(s-1) {
        let mut C: Digit = 0;
        for j in 0..=(s-1) {
            t[j] = mac(t[j], a[j], b[i], &mut C);
        }
        ts = mac(ts, 0, 0, &mut C);
        ts1 = C;

        C = 0;
        let m = t[0].wrapping_mul(n_prime_0);

        for j in 0..=(s-1) {
            t[j] = mac(t[j], m, n[j], &mut C);
        }
        ts = mac(ts, 0, 0, &mut C);
        ts1 = mac(ts1, 0, 0, &mut C);

        for j in 0..(s-1) {
            t[j] = t[j + 1]
        }
        t[s-1] = ts;
        ts = ts1;
    }

    conditionally_subtract_n(&t, ts, n)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::fixtures::*;
    use hex_literal::hex;

    #[test]
    fn montgomery_multiplication() {
        let p = p256();
        let a = q256();
        let b = c256();
        let q0 = q0_for_p(&p);

        assert_eq!(q0.wrapping_mul(p[0]), (0 as Digit).wrapping_sub(1));
        // assert_eq!(q0.wrapping_mul(p[0]), (1 as Digit).wrapping_neg());

        // GP/PARI: printf("%x", lift(-1/Mod(p0, 1 << 32)))
        // assert_eq!(q0, 0x97af00b7);
        // assert_eq!(q0, 0x70940b4697af00b7);

        let expected = Short256::from_bytes(&hex!("76902a464b9f6c0ecfc7f4db48e6c72cc08085cc9c7ab4b11a8a7e2fb418107d"));
        // This is for debugging, when the Mongomery product function
        // is modified to return early before the conditional subtraction,
        // returning just the first s digits
        // let truncated_non_reduced = Short256::from_bytes(&hex!("544bbf376697a739aecade3d06419e778aa82e8a1b6391bdc6240dc830e83376"));

        // SOS
        let m = sos_montgomery_product(a.as_ref().as_ref(), &b, &p, q0);
        // assert_ne!(m, truncated_non_reduced);

        assert_eq!(m, expected);
        // assert_eq!(&*m, &*expected);

        // CIOS
        let m = cios_montgomery_product(a.as_ref().as_ref(), &b, &p, q0);
        // assert_eq!(m, truncated_non_reduced);
        assert_eq!(m, expected);

        // assert_eq!(m, expected);

        // // Incomplete Reduction...
        // let m = montgomery_multiply(a.as_ref().as_ref(), &b, &p, q0);

        // // GP/PARI: printf("%x", lift(Mod(a, p) * Mod(b, p) / Mod(1 << 256, p)))
        // let expected = Short256::from_bytes(&hex!("76902a464b9f6c0ecfc7f4db48e6c72cc08085cc9c7ab4b11a8a7e2fb418107d"));

        // // TODO: fixme (SHOULD BE EQUAL!!! `ne` only to prevent "unused" warnings)
        // // assert_eq!(&*m, &*expected);
        // // assert_ne!(&*m, &*expected);

        // // // GP/PARI: printf("%x", lift(Mod(a, p) * Mod(b, p) / Mod(1 << 256, p)) + p)
        // // // -> 0x1_544bbf376697a739aecade3d06419e778aa82e8a1b6391bdc6240dc830e83376
        // let truncated_non_reduced_result = Short256::from_bytes(&hex!("544bbf376697a739aecade3d06419e778aa82e8a1b6391bdc6240dc830e83376"));
        // assert_eq!(m, truncated_non_reduced_result);
    }

    #[test]
    fn to_modular() {
        let p = p256();

        // Check that "1.to_modular() = R^{-1} works, i.e.: `Montgomery { y: 1, n: &p}.to_modular() = R^{-1}`
        let montgomery1 = Montgomery { y: Short256::from(1).modulo(&p).canonical_lift(), n: &p };
        let modular1 = montgomery1.to_modular();
        assert_eq!(
            modular1.x,
            // hex(lift(1/Mod(R, p)))
            Short256::from_bytes(&hex!("bfb1a42641b2bde4ee211b270ec59e39f54da8c5ed1723bc2ac70e40b6d8bf2a"))
        );

    }

    #[test]
    fn to_montgomery() {
        let p = p256();
        // let x = c256();

        // Check that "R (mod p)" works
        let r_mod_p: Short256 = R_mod_p(p.as_ref());
        assert_eq!(
            r_mod_p,
            Short256::from_bytes(&hex!("22446b0ee507c4d520fd169e42a528b535d85742811722f354667067832fdd07"))
        );

        // Check that "R^2 (mod p)" works
        let r_squared_mod_p: Short256 = R2_mod_p(p.as_ref());
        assert_eq!(
            r_squared_mod_p,
            Short256::from_bytes(&hex!("4ecdbb8d65834ef627fc1e45ba4c5229d38b34227250b466011b26f98c090f44"))
        );

        // Check that "1.to_montgomery() = R" works, i.e.: `Modular { y: 1, n: &p}.to_montgomery() = R`
        let short1 = Short256::from(1);
        assert_eq!(short1, Short256::from_bytes(&hex!("01")));

        let modular1 = Short256::from(1).modulo(&p);
        assert_eq!(modular1.x, Short256::from_bytes(&hex!("01")));
        let montgomery1 = modular1.to_montgomery();
        assert_eq!(
            montgomery1.y,
            // hex(lift(Mod(R, p)))
            Short256::from_bytes(&hex!("22446b0ee507c4d520fd169e42a528b535d85742811722f354667067832fdd07"))
        );

        // let modular = x.modulo(&p);
        // let montgomery = modular.to_montgomery();

    }

    #[test]
    fn f4_inverse_digit() {

        let e = crate::F4::DIGIT;


        let candidate = e_inverse_digit_joye_paillier(e);
        assert_eq!(candidate.wrapping_mul(e), 1);

        #[cfg(feature = "u32")]
        assert_eq!(candidate, 4294901761);
        #[cfg(feature = "u64")]
        assert_eq!(candidate, 18446462603027742721);

        #[cfg(not(debug_assertions))]
        let range = 1..=(u32::MAX as usize);
        // in debug mode, inversion is too slow to test every possible argument
        #[cfg(debug_assertions)]
        let range = e..=(e + 101);

        for odd_number in range.step_by(2) {
            let candidate = e_inverse_digit_joye_paillier(odd_number as Digit);
            assert_eq!(candidate.wrapping_mul(odd_number as Digit), 1);
        }


        let candidate = x_inverse_digit_dusse_kaliski(crate::F4::DIGIT);
        assert_eq!(candidate.wrapping_mul(crate::F4::DIGIT), 1);

        #[cfg(feature = "u32")]
        assert_eq!(candidate, 4294901761);
        #[cfg(feature = "u64")]
        assert_eq!(candidate, 18446462603027742721);

        // too slow for full test, even in release mode
        let range = e..=(e + 101);

        for odd_number in range.step_by(2) {
            let candidate = x_inverse_digit_dusse_kaliski(odd_number as Digit);
            assert_eq!(candidate.wrapping_mul(odd_number as Digit), 1);
        }

    }

}
