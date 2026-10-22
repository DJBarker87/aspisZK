#![no_std]
pub mod field;
pub mod transport;
pub mod weights;

/// Reachability harness only; field arithmetic sources remain byte-identical.
pub fn focused_qm31_mul(x: field::QM31, y: field::QM31) -> field::QM31 { x.mul(y) }
