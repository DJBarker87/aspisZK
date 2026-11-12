//! UNPROVED COST PROBE. Byte-equivalence experiment for the R0 K sampler.
use aspis_core::circle::{secure_ood_circle_point_from_parameter, SecureCirclePoint};
use aspis_core::field::{WideExact, CM31, M31, P, QM31};
pub use aspis_core::r0_transcript::CircleRow;

/// Divide a little-endian word array by P, retaining every quotient word.
/// Dividends are below P * 2^32, so every division fits in u64.
fn qm31_div_pass(mut rank: [u32; 8]) -> ([u32; 8], u32) {
    let mut remainder = 0u64;
    let mut j = 8usize;
    while j > 0 {
        j -= 1;
        let dividend = (remainder << 32u32) | u64::from(rank[j]);
        rank[j] = (dividend / u64::from(P)) as u32;
        remainder = dividend % u64::from(P);
    }
    (rank, remainder as u32)
}

/// The low four base-P digits already represent rank modulo P^4.
fn qm31_digits(block: &[u8; 32]) -> [u32; 4] {
    let mut rank = [0u32; 8];
    let mut i = 0usize;
    while i < 8 {
        let start = 4 * i;
        rank[i] = u32::from_le_bytes([
            block[start],
            block[start + 1],
            block[start + 2],
            block[start + 3],
        ]);
        i += 1;
    }
    let mut digits = [0u32; 4];
    let mut i = 0usize;
    while i < 4 {
        let (quotient, digit) = qm31_div_pass(rank);
        rank = quotient;
        digits[i] = digit;
        i += 1;
    }
    digits
}

pub fn qm31_sample(block: &[u8; 32]) -> QM31 {
    let digits = qm31_digits(block);
    QM31 {
        c0: CM31::new(M31(digits[0]), M31(digits[1])),
        c1: CM31::new(M31(digits[2]), M31(digits[3])),
    }
}

/// Return the low eight base-P digits of the 256-bit little-endian block and
/// the remaining quotient. This uses eight long divisions by P rather than
/// first reducing the full block with 256 binary steps.
///
/// Index loops only (Aspis, 2026-11-11). The body is the indexed form that the
/// R1 proof already models (research evidence `prover-commit25-20261021`,
/// `harness/lowdigits25.rs`, module `reference`): the limbs are read with a
/// `while` loop and each of the eight passes is `qm31_div_pass`. The earlier
/// form read the limbs with `core::array::from_fn` and divided through
/// `quotient.iter_mut().rev()` inside a second `from_fn` closure; the
/// Rust-to-Lean translator in use drops a write made through a reversed mutable
/// iterator without reporting an error. Same limbs, same eight division passes
/// from the high limb down, same digits and quotient:
/// `low_digits_index_tests` keeps the earlier form as an oracle.
fn low_base_p_digits(block: &[u8; 32]) -> ([u32; 8], u32) {
    let mut rank = [0u32; 8];
    let mut i = 0usize;
    while i < 8 {
        let start = 4 * i;
        rank[i] = u32::from_le_bytes([
            block[start],
            block[start + 1],
            block[start + 2],
            block[start + 3],
        ]);
        i += 1;
    }

    let mut digits = [0u32; 8];
    let mut i = 0usize;
    while i < 8 {
        let (quotient, digit) = qm31_div_pass(rank);
        rank = quotient;
        digits[i] = digit;
        i += 1;
    }
    (digits, rank[0])
}

fn decode8(digits: [u32; 8]) -> WideExact {
    WideExact::new(
        QM31 {
            c0: CM31::new(M31(digits[0]), M31(digits[1])),
            c1: CM31::new(M31(digits[2]), M31(digits[3])),
        },
        QM31 {
            c0: CM31::new(M31(digits[4]), M31(digits[5])),
            c1: CM31::new(M31(digits[6]), M31(digits[7])),
        },
    )
}

/// Add a small integer to a base-P digit vector. Returns the carry beyond
/// the final digit, which is at most one for the values used by the sampler.
///
/// Index loop (Aspis, 2026-11-11): the indexed form the R1 proof already models
/// (`harness/addsmall25.rs`, module `reference`). The earlier form iterated
/// `for digit in digits`; `low_digits_index_tests` keeps it as an oracle.
fn add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
    let mut i: usize = 0;
    while i < 8 {
        let sum = u64::from(digits[i]) + u64::from(addend);
        digits[i] = (sum % u64::from(P)) as u32;
        addend = (sum / u64::from(P)) as u32;
        i += 1;
    }
    debug_assert!(addend <= 1);
    addend != 0
}

/// `decode8(rank(block) mod P^8)`, byte-for-byte equivalent to the frozen
/// R0 sampler. The repeated divisions directly produce the low eight digits.
pub fn ordinary_sample(block: &[u8; 32]) -> WideExact {
    let (digits, _) = low_base_p_digits(block);
    decode8(digits)
}

/// `decode8((rank(block) mod (P^8 - 1)) + 1)`, byte-for-byte equivalent to
/// the frozen R0 sampler. Since `P^8 ≡ 1 (mod P^8 - 1)`, the high quotient can
/// be added to the low digits before the final increment. A carry past digit
/// seven contributes one more modulo `P^8 - 1`.
pub fn gamma_sample(block: &[u8; 32]) -> WideExact {
    let (mut digits, quotient) = low_base_p_digits(block);
    let wrapped = add_small_base_p(&mut digits, quotient + 1);
    if wrapped {
        let wrapped_again = add_small_base_p(&mut digits, 1);
        debug_assert!(!wrapped_again);
    }
    decode8(digits)
}

pub fn circle_sample(block: &[u8; 32], row: CircleRow) -> SecureCirclePoint {
    secure_ood_circle_point_from_parameter(qm31_sample(block)).unwrap_or_else(|_| {
        aspis_core::transcript::circle_fallback_point(match row {
            CircleRow::First => 0,
            CircleRow::Second => 1,
        })
    })
}

#[cfg(test)]
mod qm31_index_tests {
    use super::*;

    // Preserve the complete pre-refactor implementation as a differential oracle.
    fn old_sample(block: &[u8; 32]) -> QM31 {
        let mut rank: [u32; 8] =
            core::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
        let digits: [u32; 4] = core::array::from_fn(|_| {
            let mut remainder = 0u64;
            for limb in rank.iter_mut().rev() {
                let dividend = (remainder << 32) | u64::from(*limb);
                *limb = (dividend / u64::from(P)) as u32;
                remainder = dividend % u64::from(P);
            }
            remainder as u32
        });
        QM31 {
            c0: CM31::new(M31(digits[0]), M31(digits[1])),
            c1: CM31::new(M31(digits[2]), M31(digits[3])),
        }
    }

    fn old_pass(mut rank: [u32; 8]) -> ([u32; 8], u32) {
        let mut remainder = 0u64;
        for limb in rank.iter_mut().rev() {
            let dividend = (remainder << 32) | u64::from(*limb);
            *limb = (dividend / u64::from(P)) as u32;
            remainder = dividend % u64::from(P);
        }
        (rank, remainder as u32)
    }

    fn check(block: &[u8; 32]) {
        assert_eq!(qm31_sample(block), old_sample(block));
        let digits = qm31_digits(block);
        assert!(digits.iter().all(|&d| d < P));
        let q = qm31_sample(block);
        assert_eq!([q.c0.a.0, q.c0.b.0, q.c1.a.0, q.c1.b.0], digits);
        let mut rank = core::array::from_fn(|i| {
            u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap())
        });
        for _ in 0..4 {
            let actual = qm31_div_pass(rank);
            assert_eq!(actual, old_pass(rank), "complete quotient and remainder");
            rank = actual.0;
        }
    }

    #[test]
    fn quotient_writeback_and_sampler_match_at_word_boundaries() {
        check(&[0; 32]);
        check(&[0xff; 32]);
        for i in 0..8 {
            for word in [0, 1, P - 1, P, P + 1, u32::MAX] {
                let mut block = [0; 32];
                block[4 * i..4 * i + 4].copy_from_slice(&word.to_le_bytes());
                check(&block);
            }
        }
        for bit in 0..256 {
            let mut block = [0; 32];
            block[bit / 8] = 1 << (bit % 8);
            check(&block);
        }
    }

    #[test]
    fn sampler_matches_independent_u128_base_p_digits() {
        let p = u128::from(P);
        for rank in [0, 1, p - 1, p, p + 1, p * p - 1, p * p, p.pow(4) - 1, p.pow(4)] {
            let mut block = [0; 32];
            block[..16].copy_from_slice(&rank.to_le_bytes());
            let mut remainder = rank;
            let expected = core::array::from_fn(|_| {
                let digit = (remainder % p) as u32;
                remainder /= p;
                digit
            });
            assert_eq!(qm31_digits(&block), expected);
            check(&block);
        }
    }

    #[test]
    fn quotient_writeback_and_sampler_match_deterministic_blocks() {
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        for _ in 0..4096 {
            let mut block = [0; 32];
            for chunk in block.chunks_exact_mut(8) {
                state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = state;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                z ^= z >> 31;
                chunk.copy_from_slice(&z.to_le_bytes());
            }
            check(&block);
        }
    }
}

#[cfg(test)]
mod low_digits_index_tests {
    use super::*;

    // The complete pre-rewrite implementation, kept verbatim as a differential oracle.
    fn old_low_base_p_digits(block: &[u8; 32]) -> ([u32; 8], u32) {
        let mut quotient: [u32; 8] =
            core::array::from_fn(|i| u32::from_le_bytes(block[4 * i..4 * i + 4].try_into().unwrap()));
        let digits = core::array::from_fn(|_| {
            let mut remainder = 0u64;
            for limb in quotient.iter_mut().rev() {
                let dividend = (remainder << 32) | u64::from(*limb);
                *limb = (dividend / u64::from(P)) as u32;
                remainder = dividend % u64::from(P);
            }
            remainder as u32
        });
        assert!(quotient[1..].iter().all(|&limb| limb == 0));
        assert!(quotient[0] <= 256);
        (digits, quotient[0])
    }

    // The pre-rewrite `add_small_base_p`, kept verbatim as a differential oracle.
    fn old_add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
        for digit in digits {
            let sum = u64::from(*digit) + u64::from(addend);
            *digit = (sum % u64::from(P)) as u32;
            addend = (sum / u64::from(P)) as u32;
        }
        addend != 0
    }

    fn check(block: &[u8; 32]) {
        let new = low_base_p_digits(block);
        assert_eq!(new, old_low_base_p_digits(block));
        // `add_small_base_p` on the digits this block gives, with the addends the sampler uses
        // (quotient + 1, then 1) and with values at the ends of its range.
        for addend in [0u32, 1, new.1 + 1, 257, P - 1, P, u32::MAX] {
            let (mut a, mut b) = (new.0, new.0);
            // The sampler's digits are below P; the largest addend can overflow a digit sum only
            // beyond u64, which cannot happen for u32 inputs.
            let (ca, cb) = (add_small_base_p(&mut a, addend), old_add_small_base_p(&mut b, addend));
            assert_eq!((a, ca), (b, cb));
        }
        assert_eq!(
            ordinary_sample(block).to_le_bytes(),
            decode8(old_low_base_p_digits(block).0).to_le_bytes()
        );
    }

    fn splitmix(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = *state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    #[test]
    fn index_form_matches_iterator_form_at_boundaries() {
        check(&[0u8; 32]);
        check(&[0xFFu8; 32]);
        // Every single bit, and every block with the bits below one position set.
        for bit in 0..256usize {
            let mut one = [0u8; 32];
            one[bit / 8] = 1 << (bit % 8);
            check(&one);
            let mut below = [0u8; 32];
            for b in 0..bit {
                below[b / 8] |= 1 << (b % 8);
            }
            check(&below);
        }
        // Every limb set to values around the modulus and the word boundary, alone and in all limbs.
        for value in [0u32, 1, P - 1, P, P + 1, u32::MAX - 1, u32::MAX, 1 << 31, (1 << 31) + 1] {
            let mut all = [0u8; 32];
            for limb in 0..8usize {
                all[4 * limb..4 * limb + 4].copy_from_slice(&value.to_le_bytes());
                let mut single = [0u8; 32];
                single[4 * limb..4 * limb + 4].copy_from_slice(&value.to_le_bytes());
                check(&single);
            }
            check(&all);
        }
    }

    #[test]
    fn index_form_matches_iterator_form_on_deterministic_blocks() {
        let mut state = 0x4153_5049_5300_0001u64;
        for _ in 0..200_000 {
            let mut block = [0u8; 32];
            for chunk in block.chunks_exact_mut(8) {
                chunk.copy_from_slice(&splitmix(&mut state).to_le_bytes());
            }
            check(&block);
        }
    }
}
