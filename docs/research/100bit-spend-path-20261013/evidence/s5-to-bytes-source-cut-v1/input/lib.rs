#![no_std]
pub mod field;

/// A typed extraction root that calls the source method without altering it.
pub fn wide_exact_to_le_bytes_entry(x: field::WideExact) -> [u8; 32] {
    x.to_le_bytes()
}
