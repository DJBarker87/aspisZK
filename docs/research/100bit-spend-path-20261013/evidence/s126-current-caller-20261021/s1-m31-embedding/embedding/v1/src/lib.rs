#![no_std]
use aspis_core::{field::{M31,WideExact},r0::CodeField};
pub fn source_from_m31(value:M31)->WideExact {<WideExact as CodeField>::from_m31(value)}
