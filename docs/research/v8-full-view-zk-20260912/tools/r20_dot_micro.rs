//! Pure source-local microbenchmark kernels for a host/SBF research harness.
//! The caller owns runtime vectors, timing, CU logging, and equality checks.
extern crate aspis_core as corelib;
#[path = "r20_whole_dot.rs"]
mod r20_whole_dot;
#[path="r20_private_dot_adapter.rs"]
mod r20_private_dot_adapter;

use corelib::field::{PreparedQm31Multiplier, QM31};
use r20_whole_dot::dot;

#[inline(never)]
fn scalar(a: &[QM31], b: &[QM31]) -> QM31 {
    a.iter()
        .zip(b)
        .fold(QM31::ZERO, |s, (&x, &y)| s.add(x.mul(y)))
}

#[inline(never)]
fn batches4(a: &[QM31], b: &[QM31]) -> QM31 {
    let mut out = QM31::ZERO;
    let common = a.len() / 4 * 4;
    for start in (0..common).step_by(4) {
        out = out.add(corelib::field::qm31_sum_products4(
            a[start..start + 4].try_into().unwrap(),
            b[start..start + 4].try_into().unwrap(),
        ));
    }
    for (&x, &y) in a[common..].iter().zip(&b[common..]) {
        out = out.add(x.mul(y));
    }
    out
}

#[inline(never)]
fn prepared3_blocks(a: &[QM31], b: &[QM31]) -> QM31 {
    let mut out = QM31::ZERO;
    let common = a.len() / 3 * 3;
    for start in (0..common).step_by(3) {
        let source: [QM31; 3] = a[start..start + 3].try_into().unwrap();
        let prepared: [PreparedQm31Multiplier; 3] = source.map(PreparedQm31Multiplier::new);
        out = out.add(corelib::field::qm31_sum_products3_prepared(
            &prepared,
            b[start..start + 3].try_into().unwrap(),
        ));
    }
    for (&x, &y) in a[common..].iter().zip(&b[common..]) {
        out = out.add(x.mul(y));
    }
    out
}

/// Select one arithmetic path over caller-owned runtime vectors.
/// Modes: 0 scalar, 1 existing batches-of-four with leftover, 2 prepared-3
/// blocks with leftover, 3 whole-dot.  The harness should black-box inputs and
/// outputs, invoke all modes on lengths 3/4/6/16/27/163, and assert equality.
#[inline(never)]
pub fn run(left: &[QM31], right: &[QM31], mode: u8) -> QM31 {
    assert_eq!(left.len(), right.len());
    match mode {
        0 => scalar(left, right),
        1 => batches4(left, right),
        2 => prepared3_blocks(left, right),
        3 => dot(left, right).unwrap(),
        4 => r20_private_dot_adapter::dot(left,right).unwrap(),
        _ => panic!("invalid R20 dot micro mode"),
    }
}

#[inline(never)]
pub fn assert_equal_all(left: &[QM31], right: &[QM31]) -> QM31 {
    let reference = run(left, right, 0);
    for mode in 1..=4 {
        assert_eq!(reference, run(left, right, mode), "R20 dot mode {mode}");
    }
    reference
}
