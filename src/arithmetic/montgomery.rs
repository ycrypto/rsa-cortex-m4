use crate::Digit;
use crate::numbers::Bits;

#[inline]
fn mod_two(x: Digit, i: usize) -> Digit {
    x & (((1 as Digit) << i) - 1)
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
        let two_to_the_i_minus_1 = (1 as Digit) << (i - 1);
        if mod_two(x.wrapping_mul(y), i) >= two_to_the_i_minus_1 {
            y = y.wrapping_add(two_to_the_i_minus_1);
        }
    }

    let two_to_the_b_minus_1 = (1 as Digit) << (Digit::BITS - 1);
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn f4_inverse_digit() {

        let e = crate::F4;


        let candidate = e_inverse_digit_joye_paillier(e);
        assert_eq!(candidate.wrapping_mul(e), 1);

        #[cfg(any(target_pointer_width = "32", feature = "u32"))]
        assert_eq!(candidate, 4294901761);
        #[cfg(all(target_pointer_width = "64", not(feature = "u32")))]
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


        let candidate = x_inverse_digit_dusse_kaliski(crate::F4);
        assert_eq!(candidate.wrapping_mul(crate::F4), 1);

        #[cfg(any(target_pointer_width = "32", feature = "u32"))]
        assert_eq!(candidate, 4294901761);
        #[cfg(all(target_pointer_width = "64", not(feature = "u32")))]
        assert_eq!(candidate, 18446462603027742721);

        // too slow for full test, even in release mode
        let range = e..=(e + 101);

        for odd_number in range.step_by(2) {
            let candidate = x_inverse_digit_dusse_kaliski(odd_number as Digit);
            assert_eq!(candidate.wrapping_mul(odd_number as Digit), 1);
        }

    }

}
