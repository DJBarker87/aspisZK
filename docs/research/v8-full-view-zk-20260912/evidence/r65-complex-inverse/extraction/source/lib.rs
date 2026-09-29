//! Extraction-only entry; selected field sources are copied unchanged.
#![allow(dead_code, unexpected_cfgs)]
pub mod field;
pub fn complex_inverse_probe(x: field::CM31) -> field::CM31 {
    x.inv()
}
