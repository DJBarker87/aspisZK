//! Extraction-only entry point; selected field sources are copied unchanged.
#![allow(dead_code, unexpected_cfgs)]
pub mod field;
pub fn inverse_probe(x: field::M31) -> field::M31 {
    x.inv()
}
