//! Owned, safe proof references. No syscall or C ABI implementation is replaced.
#![cfg(kani)]
#![cfg_attr(not(feature="extraction"), feature(formatting_options))]
#[cfg(not(feature="world-only"))]
pub mod coefficients;
#[cfg(not(any(feature="copy-only",feature="world-only")))]
pub mod row;
#[cfg(not(feature="copy-only"))]
pub mod world;
#[cfg(not(feature="extraction"))]
mod native;

