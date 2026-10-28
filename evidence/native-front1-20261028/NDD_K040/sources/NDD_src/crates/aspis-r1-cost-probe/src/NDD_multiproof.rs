use super::*;
#[path="NDD_reference.rs"] pub(super) mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub(super) fn verdict(v:bool)->bool{if cfg!(NDD_negative_verifier){!v}else{v}}
#[kani::proof_for_contract(index_at)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn index_contract(){let x:[u32;16]=kani::any();index_at(&x,kani::any());}
#[kani::proof_for_contract(value_at)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn value_contract(){let x:[[u8;32];16]=kani::any();value_at(&x,kani::any());}
#[kani::proof_for_contract(root_matches)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn root_contract(){let x:[[u8;32];16]=kani::any();let r:[u8;32]=kani::any();root_matches(&x,&r);}
#[cfg(NDD_bits)] #[kani::proof_for_contract(Arity::bits)]
fn bits_contract(){let x=if kani::any(){Arity::Eight}else{Arity::Two};x.bits();}
