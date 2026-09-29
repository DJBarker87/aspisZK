//! Extraction-only entry; selected field and circle sources copied unchanged.
#![allow(dead_code, unexpected_cfgs)]
pub mod field;
pub mod circle;
pub fn circle_probe(x: field::QM31) -> Result<circle::SecureCirclePoint, circle::CirclePointError> {
    circle::secure_ood_circle_point_from_parameter(x)
}
