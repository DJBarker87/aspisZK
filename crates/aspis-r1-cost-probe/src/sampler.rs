//! UNPROVED COST PROBE. Byte-equivalence experiment for the R0 K sampler.
use aspis_core::circle::{secure_ood_circle_point_from_parameter, SecureCirclePoint};
use aspis_core::field::{CM31, M31, P, QM31};
pub use aspis_core::r0_transcript::CircleRow;

/// The low four base-P digits already represent rank modulo P^4.
/// Dividends are below P * 2^32, so every division fits in u64.
pub fn qm31_sample(block: &[u8; 32]) -> QM31 {
    let mut rank: [u32; 8] = core::array::from_fn(|i| {
        u32::from_le_bytes(block[4*i..4*i+4].try_into().unwrap())
    });
    let digits: [u32; 4] = core::array::from_fn(|_| {
        let mut remainder = 0u64;
        for limb in rank.iter_mut().rev() {
            let dividend = (remainder << 32) | u64::from(*limb);
            *limb = (dividend / u64::from(P)) as u32;
            remainder = dividend % u64::from(P);
        }
        remainder as u32
    });
    QM31 { c0: CM31::new(M31(digits[0]), M31(digits[1])),
           c1: CM31::new(M31(digits[2]), M31(digits[3])) }
}

pub fn circle_sample(block: &[u8; 32], row: CircleRow) -> SecureCirclePoint {
    secure_ood_circle_point_from_parameter(qm31_sample(block)).unwrap_or_else(|_| {
        aspis_core::transcript::circle_fallback_point(match row {
            CircleRow::First => 0, CircleRow::Second => 1,
        })
    })
}
