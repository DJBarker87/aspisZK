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
        let dividend = (remainder << 32) | u64::from(rank[j]);
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
fn low_base_p_digits(block: &[u8; 32]) -> ([u32; 8], u32) {
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

    // After eight divisions, the quotient is at most 256 and fits in u32.
    debug_assert!(quotient[1..].iter().all(|&limb| limb == 0));
    debug_assert!(quotient[0] <= 256);
    (digits, quotient[0])
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
fn add_small_base_p(digits: &mut [u32; 8], mut addend: u32) -> bool {
    for digit in digits {
        let sum = u64::from(*digit) + u64::from(addend);
        *digit = (sum % u64::from(P)) as u32;
        addend = (sum / u64::from(P)) as u32;
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

pub fn low_for_audit(b:&[u8;32])->([u32;8],u32){low_base_p_digits(b)}
pub fn add_for_audit(mut ds:[u32;8],n:u32)->(bool,[u32;8]){let wrapped=add_small_base_p(&mut ds,n);(wrapped,ds)}
