//! UNPROVED COST PROBE. Byte-equivalence experiment for the R0 K sampler.
use aspis_core::circle::{secure_ood_circle_point_from_parameter, SecureCirclePoint};
use aspis_core::field::{WideExact, CM31, M31, P, QM31};
pub use aspis_core::r0_transcript::CircleRow;

/// The low four base-P digits already represent rank modulo P^4.
/// Dividends are below P * 2^32, so every division fits in u64.
pub fn qm31_sample(block: &[u8; 32]) -> QM31 {
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
