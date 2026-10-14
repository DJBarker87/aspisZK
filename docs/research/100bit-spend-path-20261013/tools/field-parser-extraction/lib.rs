//! Extraction-only entry point. The complete field sources are copied unchanged.
#![no_std]
#![allow(dead_code, unexpected_cfgs)]

pub mod field;

pub fn parse_m31_probe(base: [u8; 4]) -> Option<field::M31> {
    field::M31::from_le_bytes(base)
}

pub fn parse_fields_probe(
    base: [u8; 4],
    quadratic: &[u8],
    quartic: &[u8],
) -> (Option<field::M31>, Option<field::CM31>, Option<field::QM31>) {
    (
        field::M31::from_le_bytes(base),
        field::CM31::from_le_bytes(quadratic),
        field::QM31::from_le_bytes(quartic),
    )
}
