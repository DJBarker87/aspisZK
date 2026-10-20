#![allow(dead_code, unused_mut, unexpected_cfgs, private_interfaces)]
use aspis_core::r0::CodeField;
include!("frozen.rs");
use compact::OPENING;
include!("owned.rs");
include!("geometry_owned.rs");
#[cfg(any(test,kani))]
mod support;
#[cfg(test)] mod tests;
#[cfg(kani)] mod proofs;
