extern crate alloc;
use super::*;
use aspis_r1_cost_probe::r1_wire::{SemanticTranscript,Error};
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
type RecordReply=Result<SemanticTranscript<SolanaDigest>,Error>;
type ArrayReply=Result<[u8;32],Error>;
#[kani::ensures(|r| r.is_err())]
fn record_inverted(x:[u8;32])->RecordReply {Ok(aspis_r1_cost_probe::r1_wire::NDI_build(SolanaDigest,x,0))}
#[kani::ensures(|_| true)]
fn record_weak(x:[u8;32])->RecordReply {Ok(aspis_r1_cost_probe::r1_wire::NDI_build(SolanaDigest,x,0))}
#[kani::modifies(&mut x[0])]
fn record_badframe(x:&mut [u8;2])->RecordReply {x[1]=x[1].wrapping_add(1);Ok(aspis_r1_cost_probe::r1_wire::NDI_build(SolanaDigest,[0;32],0))}
#[kani::proof_for_contract(record_inverted)] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn record_invert(){let _=record_inverted(kani::any());}
#[kani::proof_for_contract(record_weak)] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn record_weak_proof(){let _=record_weak(kani::any());}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn record_real(){let x:[u8;32]=kani::any();assert!(matches!(record_weak(x),Ok(t) if t.state()==x));}
#[kani::proof] #[kani::stub_verified(record_weak)] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn record_unimplied(){let x:[u8;32]=kani::any();assert!(matches!(record_weak(x),Ok(t) if t.state()==x));}
#[kani::proof_for_contract(record_badframe)] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn record_frame(){let mut x:[u8;2]=kani::any();let _=record_badframe(&mut x);}

#[kani::ensures(|r| r.is_err())] fn array_inverted(x:[u8;32])->ArrayReply {Ok(x)}
#[kani::ensures(|_| true)] fn array_weak(x:[u8;32])->ArrayReply {Ok(x)}
#[kani::modifies(&mut x[0])] fn array_badframe(x:&mut [u8;2])->ArrayReply {x[1]=x[1].wrapping_add(1);Ok([0;32])}
#[kani::proof_for_contract(array_inverted)] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_invert(){let _=array_inverted(kani::any());}
#[kani::proof_for_contract(array_weak)] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_weak_proof(){let _=array_weak(kani::any());}
#[kani::proof] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_real(){let x:[u8;32]=kani::any();assert!(matches!(array_weak(x),Ok(t) if t==x));}
#[kani::proof] #[kani::stub_verified(array_weak)] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_unimplied(){let x:[u8;32]=kani::any();assert!(matches!(array_weak(x),Ok(t) if t==x));}
#[kani::proof_for_contract(array_badframe)] #[kani::unwind(40)] #[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn array_frame(){let mut x:[u8;2]=kani::any();let _=array_badframe(&mut x);}
