#![no_std]
extern crate alloc;

// Exact byte copies of crates/aspis-core/src/field.rs and its
// crates/aspis-core/src/field/wide_exact.rs child are pinned in source-pins.json.
pub mod field;

pub mod weights {
    use crate::field::WideExact as E;

    // Exact 90-byte body/declaration copied from candidate and frozen weights.rs.
    pub fn field(bytes:&[u8],i:usize)->E { E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap() }
}
