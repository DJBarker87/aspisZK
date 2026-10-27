extern crate alloc;
use alloc::boxed::Box;
use aspis_core::field::QM31 as K;
use aspis_r1_cost_probe::r1_wire::Error;
include!("XRg_reference.rs");
include!("XRg_stages.rs");
#[cfg(kani)] mod XRg_harnesses;
