#![no_std]
extern crate self as aspis_core;
pub mod field;
pub mod circle;

/// Transparent extraction root; no implementation or arithmetic substitution.
pub fn secure_circle_producer(parameter: field::QM31) -> Result<circle::SecureCirclePoint, circle::CirclePointError> {
    circle::secure_ood_circle_point_from_parameter(parameter)
}
