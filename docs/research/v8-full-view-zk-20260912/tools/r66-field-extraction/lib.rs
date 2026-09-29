//! Extraction-only entry; selected field sources are copied unchanged.
#![allow(dead_code, unexpected_cfgs)]
pub mod field;
pub fn quartic_inverse_probe(x: field::QM31) -> Option<field::QM31> {
    x.try_inv()
}
