#![no_std]
extern crate alloc;
pub mod sampler;
pub mod r1_wire;
mod r1_semantic {
 // Diagnostic assertion formatting change only; original native step is unchanged.
 macro_rules! assert_eq { ($left:expr,$right:expr $(,)?) => { assert!($left == $right) }; }
 use crate::r1_wire::{self as wire,Error};
 use alloc::boxed::Box;
 use aspis_core::field::QM31;
 #[cfg(kani)]
 #[path="../claims_write_proofs.rs"]
 mod claims_write_proofs;
}
