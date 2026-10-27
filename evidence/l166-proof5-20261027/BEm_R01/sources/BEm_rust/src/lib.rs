#![allow(dead_code, unexpected_cfgs, non_snake_case)]
include!("BEm_frozen.rs");
#[cfg(kani)]
mod BEm_reference;

#[cfg(test)]
mod BEm_nativefixtures;

// Extraction-only entry points for the same owned recorder; never shipped.
#[cfg(BEm_extract)]
mod BEm_extract;
