#![allow(dead_code, unexpected_cfgs, non_snake_case)]
include!("BEl_frozen.rs");
#[cfg(kani)]
mod BEl_reference;

#[cfg(test)]
mod BEl_nativefixtures;

// Extraction-only entry points for the same owned recorder; never shipped.
#[cfg(BEl_extract)]
mod BEl_extract;
