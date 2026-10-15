//! Isolated extraction entry point. Full field sources are copied unchanged except the selected WideExact parser body.
#![no_std]
#![allow(dead_code, unexpected_cfgs)]

pub mod field;

pub fn parse_wide_exact_probe(bytes: &[u8]) -> Option<field::WideExact> {
    field::WideExact::from_le_bytes(bytes)
}
