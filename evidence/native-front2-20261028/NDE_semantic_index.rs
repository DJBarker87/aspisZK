#[path="NDE_claim_reference.rs"] pub(super) mod claim_reference;
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::unwind(85)]
#[kani::proof_for_contract(super::selected_claim)]
fn NDE_claim(){
 // QM31, CM31 and M31 are transparent records of u32. Every bit pattern is
 // a valid Rust carrier; canonicality is unnecessary for a projection.
 let raw:[[u32;4];84]=kani::any();
 let claims=raw.map(|a|to_native(reference::Q{c0:reference::C{a:a[0],b:a[1]},c1:reference::C{a:a[2],b:a[3]}}));
 let p:usize=kani::any();let c:usize=kani::any();kani::assume(p<3&&c<28);
 let _=super::selected_claim(&claims,p,c);
}
