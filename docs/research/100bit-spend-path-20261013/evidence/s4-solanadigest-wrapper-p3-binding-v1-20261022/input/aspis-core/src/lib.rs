#![no_std]
pub type HashFn = fn(&[&[u8]]) -> [u8; 32];
mod digest;
pub use digest::Digest32;
