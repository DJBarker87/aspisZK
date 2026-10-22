#![no_std]
pub mod field;
pub mod transport;
pub mod weights;

/// Reachability harness only; field arithmetic sources remain byte-identical.
pub fn focused_qm31_mul(x: field::QM31, y: field::QM31) -> field::QM31 { x.mul(y) }

/// Reachability harness only; original field and wide_exact files remain byte-identical.
pub fn focused_wide_exact_mul(x: field::WideExact, y: field::WideExact) -> field::WideExact { x.mul(y) }
