#[path="NDE_claim_reference.rs"] pub(super) mod claim_reference;
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::selected_claim)]
fn NDE_claim(){
 // QM31, CM31 and M31 are transparent records of u32. Every bit pattern is
 // a valid Rust carrier; canonicality is unnecessary for a projection.
 let claims=unsafe{kani::any_raw::<[QM31;84]>()};
 let p:usize=kani::any();let c:usize=kani::any();kani::assume(p<3&&c<28);
 let _=super::selected_claim(&claims,p,c);
}
