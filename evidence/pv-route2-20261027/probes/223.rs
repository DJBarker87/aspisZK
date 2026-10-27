//! Candidate host-prover-only extraction leaf. See design/PV-EXTRACT-20261027.md.
use aspis_core::field::{CM31, M31, QM31};

pub fn compress_tagged_tuple(tag: M31, values: &[M31], lambda: QM31) -> QM31 {
    let mut compressed = QM31::from_cm31(CM31::from_m31(tag));
    let mut power = lambda;
    let mut i = 0usize;
    while i < values.len() {
        compressed = compressed.add(power.mul_m31(values[i]));
        power = power.mul(lambda);
        i = i.wrapping_add(1);
    }
    compressed
}
