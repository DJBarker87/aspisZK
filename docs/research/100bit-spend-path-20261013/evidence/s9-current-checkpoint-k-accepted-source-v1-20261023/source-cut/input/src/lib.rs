#![no_std]
extern crate self as aspis_core;
pub mod field;
pub mod circle;

/// Exact current checkpoint QM31 decoder. Callers use a 16-byte raw array;
/// this root retains every from_le_bytes rejection/failure on arbitrary slices.
pub fn checkpoint_qm_decoder(bytes: &[u8]) -> Option<field::QM31> {
    field::QM31::from_le_bytes(bytes)
}
