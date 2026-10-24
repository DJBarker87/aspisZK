#![allow(non_snake_case, unexpected_cfgs)]
extern crate alloc;
extern crate self as aspis_core;
pub mod field;
pub mod r0 {
    include!("r0/error.rs");
    pub mod heap;
}
pub mod transport {
    include!("variant.rs");
    // Only closes the source impl after final_len; row/permutation methods
    // are outside this call cone. No existing function body is edited.
}
pub mod verifier {
    use super::{field::{QM31 as K, WideExact as E},transport::Variant};
    use alloc::vec::Vec;
    include!("verifier_error.rs");
    include!("accumulator.rs");
    include!("pending.rs");
    // Close BatchedWeights impl after its unchanged new function.
}
// Monomorphizations only. The included generic helper and all Copy/Clone
// implementations are the unmodified source. No allocator or std stub.
pub fn Port20ALLOC_qm31(n: usize, value: field::QM31) -> Result<alloc::vec::Vec<field::QM31>,r0::Error> {
    r0::heap::filled(n,value)
}
pub fn Port20ALLOC_row(n: usize, value: [u64;4]) -> Result<alloc::vec::Vec<[u64;4]>,r0::Error> {
    r0::heap::filled(n,value)
}
