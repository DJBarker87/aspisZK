extern crate alloc;
use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof_for_contract(aspis_r1_cost_probe::r1_wire::SemanticTranscript::<SolanaDigest>::state)]
#[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn state_contract(){let _=aspis_r1_cost_probe::r1_wire::NDI_state_for_backend(SolanaDigest,kani::any(),kani::any());}
#[kani::proof] #[kani::stub_verified(aspis_r1_cost_probe::r1_wire::SemanticTranscript::<SolanaDigest>::state)]
#[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn state_caller(){let state:[u8;32]=kani::any();let out=aspis_r1_cost_probe::r1_wire::NDI_state_for_backend(SolanaDigest,state,kani::any());assert_eq!(out,state);}
#[kani::proof] #[kani::stub_verified(aspis_r1_cost_probe::r1_wire::SemanticTranscript::<SolanaDigest>::state)]
#[kani::unwind(35)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn state_wrong(){let state:[u8;32]=kani::any();let out=aspis_r1_cost_probe::r1_wire::NDI_state_for_backend(SolanaDigest,state,kani::any());assert_ne!(out,state);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_positive(){let a:[u8;32]=kani::any();let mut b:[u8;32]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<32);assert_eq!(b[i],a[i]);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn copy_negative(){let a:[u8;32]=kani::any();let mut b:[u8;32]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<32);assert_ne!(b[i],a[i]);}
