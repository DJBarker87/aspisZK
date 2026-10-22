#![no_std]
pub mod field;
pub mod transport;
pub mod weights;

/// Reachability harness only; field arithmetic sources remain byte-identical.
pub fn focused_qm31_mul(x: field::QM31, y: field::QM31) -> field::QM31 { x.mul(y) }

/// Reachability harness only; original field and wide_exact files remain byte-identical.
pub fn focused_wide_exact_mul(x: field::WideExact, y: field::WideExact) -> field::WideExact { x.mul(y) }

/// Reachability harness only; the actual QM31 square implementation is unchanged.
pub fn focused_qm31_square(x: field::QM31) -> field::QM31 { x.square() }

/// Reachability harness only; the actual mixed WideExact/QM31 implementation is unchanged.
pub fn focused_wide_exact_mul_qm31(x: field::WideExact, y: field::QM31) -> field::WideExact { x.mul_qm31(y) }
