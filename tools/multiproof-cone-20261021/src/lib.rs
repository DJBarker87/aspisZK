#![allow(dead_code, unexpected_cfgs)]
extern crate alloc;
pub mod frozen;
pub mod reference;
pub mod parser_reference;
pub mod sort_reference;
pub use frozen::r1_wire;
#[cfg(kani)] mod proofs;
#[cfg(test)] mod tests;

#[cfg(kani)] pub mod adoption;
