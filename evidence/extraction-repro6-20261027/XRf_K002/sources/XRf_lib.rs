extern crate alloc;
pub use aspis_r1_cost_probe::{r1_semantic,weights,trace,fast_pairing,compact};
use aspis_core::{Digest32,field::{WideExact as E,QM31 as K,M31}};
use aspis_r1_cost_probe::{verifier::{Error,View,Prepared,Accumulator,checkpoint_size},transport::Variant};
use weights::{field,powers};
use alloc::vec::Vec;
include!("XRf_actual.rs");
include!("XRf_reference.rs");
#[cfg(kani)]
mod XRf_harnesses;
