//! Focused actual-core check for the guarded canonical M31::mul candidate.
//! The staged field.rs is selected by the path relative to the stage root.

#[path = "crates/aspis-core/src/field.rs"]
mod field;

use field::{M31, P};

fn reference_reduce(mut x: u64) -> u32 {
    x = (x & P as u64) + (x >> 31);
    x = (x & P as u64) + (x >> 31);
    let x = x as u32;
    if x >= P { x - P } else { x }
}

fn reference_mul(a: u32, b: u32) -> u32 {
    reference_reduce((a as u64) * (b as u64))
}

fn reference_mul_u128(a: u32, b: u32) -> u32 {
    (((a as u128) * (b as u128)) % (P as u128)) as u32
}

fn next(state: &mut u64) -> u32 {
    *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    (*state >> 32) as u32
}

fn check(a: u32, b: u32, label: &str) {
    let got = M31(a).mul(M31(b)).0;
    let want = reference_mul(a, b);
    let want_u128 = reference_mul_u128(a, b);
    assert_eq!(got, want, "{label}: {a} * {b}: got {got}, want {want}");
    assert_eq!(want, want_u128, "{label}: independent u128 modulus");
}

fn main() {
    let p = P;
    let edges = [0, 1, p - 2, p - 1, p, p + 1, u32::MAX];
    for &a in &edges { for &b in &edges { check(a, b, "edge"); } }

    let mut state = 0x52419_CAFE_u64;
    for _ in 0..200_000 {
        check(next(&mut state), next(&mut state), "fullwidth");
    }

    // Exercise values constructed in the canonical range, including the
    // subtraction boundary and representative products near the upper bound.
    let canonical = [0, 1, 2, p / 2, p - 3, p - 2, p - 1];
    for &a in &canonical { for &b in &canonical { check(a, b, "canonical"); } }

    let negative = (1u64 << 62) - 1;
    assert_eq!(M31::reduce_u64(negative).0, reference_reduce(negative),
               "general reducer 2^62-1 regression");
    let one_fold_s = (negative & p as u64) + (negative >> 31);
    assert_eq!(one_fold_s, 2 * p as u64);
    assert_eq!(one_fold_s - p as u64, p as u64,
               "explicit one-fold negative control reaches s=P");
    assert_ne!((one_fold_s - p as u64) as u32, reference_reduce(negative),
                "one fold must not replace the general reducer");
    println!("R19_CANONICAL_MUL_CHECK passed=true fullwidth_pairs=200000 edge_pairs=49 canonical_pairs=49 independent_u128=true general_reduce_2^62_minus_1=true one_fold_negative_control=true");
}
