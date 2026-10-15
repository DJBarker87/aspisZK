//! Dependency-free differential harness for the narrow CM31/QM31 byte-slice
//! parser edit. The root kit supplies the exact full `baseline.rs` and
//! candidate `field.rs` modules (and each module's `wide_exact.rs` sibling).
#![allow(dead_code, unexpected_cfgs)]

#[path = "baseline.rs"]
mod baseline;
#[path = "field.rs"]
mod field;

use std::panic::{catch_unwind, AssertUnwindSafe};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Outcome<T> {
    Panic,
    None,
    Value(T),
}

#[derive(Default)]
struct Counts {
    input_vectors: usize,
    parser_comparisons: usize,
}

fn observe<T>(f: impl FnOnce() -> Option<T>) -> Outcome<T> {
    match catch_unwind(AssertUnwindSafe(f)) {
        Err(_) => Outcome::Panic,
        Ok(None) => Outcome::None,
        Ok(Some(value)) => Outcome::Value(value),
    }
}

fn cm_limbs(value: baseline::CM31) -> [u32; 2] {
    [value.a.0, value.b.0]
}

fn cm_limbs_candidate(value: field::CM31) -> [u32; 2] {
    [value.a.0, value.b.0]
}

fn qm_limbs(value: baseline::QM31) -> [u32; 4] {
    [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
}

fn qm_limbs_candidate(value: field::QM31) -> [u32; 4] {
    [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
}

fn compare(bytes: &[u8], counts: &mut Counts) {
    counts.input_vectors += 1;
    counts.parser_comparisons += 2;
    let baseline_cm = observe(|| baseline::CM31::from_le_bytes(bytes).map(cm_limbs));
    let candidate_cm = observe(|| field::CM31::from_le_bytes(bytes).map(cm_limbs_candidate));
    assert_eq!(candidate_cm, baseline_cm, "CM31 differs for len={} bytes={bytes:?}", bytes.len());

    let baseline_qm = observe(|| baseline::QM31::from_le_bytes(bytes).map(qm_limbs));
    let candidate_qm = observe(|| field::QM31::from_le_bytes(bytes).map(qm_limbs_candidate));
    assert_eq!(candidate_qm, baseline_qm, "QM31 differs for len={} bytes={bytes:?}", bytes.len());
}

fn boundary_cases(counts: &mut Counts) {
    const P: u32 = 0x7fff_ffff;
    let boundaries = [0, 1, P - 1, P, P + 1, u32::MAX];
    for len in 0..=40 {
        compare(&vec![0; len], counts);
        for limb_start in (0..len).step_by(4) {
            if limb_start + 4 > len {
                continue;
            }
            for value in boundaries {
                let mut bytes = vec![0; len];
                bytes[limb_start..limb_start + 4].copy_from_slice(&value.to_le_bytes());
                compare(&bytes, counts);
            }
        }
    }
}

fn every_single_byte_value(counts: &mut Counts) {
    // Exercise every byte value at every position that can occur in lengths
    // 0..=40. All other bytes are zero; varying the exact input length also
    // covers ignored trailing data and short-slice panic/None behavior.
    for len in 0..=40 {
        for position in 0..len {
            for value in 0..=u8::MAX {
                let mut bytes = vec![0; len];
                bytes[position] = value;
                compare(&bytes, counts);
            }
        }
    }
}

fn seeded_random_cases(counts: &mut Counts) {
    let mut state = 0x4d31_4351_4d31_2026u64;
    for len in 0..=40 {
        for _ in 0..256 {
            let mut bytes = vec![0; len];
            for byte in &mut bytes {
                // Deterministic xorshift64* stream; no external RNG dependency.
                state ^= state >> 12;
                state ^= state << 25;
                state ^= state >> 27;
                *byte = (state.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 56) as u8;
            }
            compare(&bytes, counts);
        }
    }
}

#[test]
fn cm31_qm31_candidate_matches_baseline_field_module() {
    // Panics are expected for some historical short-slice inputs; keep the
    // differential output quiet while comparing their outcome classes.
    std::panic::set_hook(Box::new(|_| {}));
    let mut counts = Counts::default();
    boundary_cases(&mut counts);
    every_single_byte_value(&mut counts);
    seeded_random_cases(&mut counts);
    eprintln!(
        "differential vectors: {}; parser comparisons: {} (CM31 + QM31 per vector)",
        counts.input_vectors, counts.parser_comparisons
    );
}
