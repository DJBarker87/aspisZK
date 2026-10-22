#![no_std]
pub mod field;
pub mod transport;
pub mod weights;

/// Reachability harness only; the body under study remains WideExact::mul_m31.
pub fn focused_wide_mul_m31(x: field::WideExact, rhs: field::M31) -> field::WideExact { x.mul_m31(rhs) }
