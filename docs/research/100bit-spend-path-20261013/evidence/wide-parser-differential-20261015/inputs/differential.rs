//! Dependency-free differential harness for the isolated WideExact byte parser.
//! The kit supplies full baseline/candidate field modules and each sibling
//! `wide_exact.rs`; this test calls their actual `WideExact::from_le_bytes`.
#![allow(dead_code, unexpected_cfgs)]

extern crate alloc;

mod baseline;
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
    parser_calls: usize,
}

fn observe(f: impl FnOnce() -> Option<[u32; 8]>) -> Outcome<[u32; 8]> {
    match catch_unwind(AssertUnwindSafe(f)) {
        Err(_) => Outcome::Panic,
        Ok(None) => Outcome::None,
        Ok(Some(value)) => Outcome::Value(value),
    }
}

fn compare(bytes: &[u8], counts: &mut Counts) -> Outcome<[u32; 8]> {
    counts.input_vectors += 1;
    counts.parser_calls += 2;
    let baseline = observe(|| baseline::WideExact::from_le_bytes(bytes).map(|x| x.to_limbs()));
    let candidate = observe(|| field::WideExact::from_le_bytes(bytes).map(|x| x.to_limbs()));
    assert!(!matches!(&baseline, Outcome::Panic), "baseline panicked for len={} bytes={bytes:?}", bytes.len());
    assert!(!matches!(&candidate, Outcome::Panic), "candidate panicked for len={} bytes={bytes:?}", bytes.len());
    assert_eq!(candidate, baseline, "WideExact differs for len={} bytes={bytes:?}", bytes.len());
    candidate
}

fn put_limb(bytes: &mut [u8; 32], limb: usize, value: u32) {
    bytes[limb * 4..limb * 4 + 4].copy_from_slice(&value.to_le_bytes());
}

fn limb_vector(values: &[u32; 8]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (i, value) in values.iter().copied().enumerate() {
        put_limb(&mut bytes, i, value);
    }
    bytes
}

fn boundary_cases(counts: &mut Counts) {
    const P: u32 = 0x7fff_ffff;
    let boundaries = [0, 1, P - 1, P, P + 1, u32::MAX];

    // Every byte length, including short and trailing-byte inputs.
    for len in 0..=64 {
        compare(&vec![0; len], counts);
    }

    // Each of the eight little-endian limbs independently at all boundary values.
    for limb in 0..8 {
        for value in boundaries {
            let mut bytes = [0u8; 32];
            put_limb(&mut bytes, limb, value);
            compare(&bytes, counts);
        }
    }

    // Pairwise combinations exercise interactions without enumerating 6^8 tuples.
    for first in 0..8 {
        for second in first + 1..8 {
            for first_value in boundaries {
                for second_value in boundaries {
                    let mut bytes = [0u8; 32];
                    put_limb(&mut bytes, first, first_value);
                    put_limb(&mut bytes, second, second_value);
                    compare(&bytes, counts);
                }
            }
        }
    }
    for value in boundaries {
        compare(&limb_vector(&[value; 8]), counts);
    }
}

fn every_single_byte_value(counts: &mut Counts) {
    for position in 0..32 {
        for value in 0..=u8::MAX {
            let mut bytes = [0u8; 32];
            bytes[position] = value;
            compare(&bytes, counts);
        }
    }
}

fn seeded_random_cases(counts: &mut Counts) {
    let mut state = 0x5749_4445_5041_5253u64;
    for len in 0..=64 {
        for _ in 0..256 {
            let mut bytes = vec![0; len];
            for byte in &mut bytes {
                state ^= state >> 12;
                state ^= state << 25;
                state ^= state >> 27;
                *byte = (state.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 56) as u8;
            }
            compare(&bytes, counts);
        }
    }
}

fn canonical_limb_cases(counts: &mut Counts) {
    const P: u32 = 0x7fff_ffff;
    let mut state = 0x4341_4e4f_4e49_4341u64;
    for _ in 0..4096 {
        let limbs = std::array::from_fn(|_| {
            state ^= state >> 12;
            state ^= state << 25;
            state ^= state >> 27;
            ((state.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 32) as u32) % P
        });
        let observed = compare(&limb_vector(&limbs), counts);
        assert_eq!(observed, Outcome::Value(limbs), "canonical limbs failed roundtrip: {limbs:?}");
    }
}

#[test]
fn wideexact_candidate_matches_baseline_field_module() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut counts = Counts::default();
    boundary_cases(&mut counts);
    every_single_byte_value(&mut counts);
    seeded_random_cases(&mut counts);
    canonical_limb_cases(&mut counts);
    assert_eq!(counts.input_vectors, 30_055);
    assert_eq!(counts.parser_calls, 60_110);
    eprintln!(
        "differential input vectors: {}; parser calls: {} (two per vector)",
        counts.input_vectors, counts.parser_calls
    );
}
