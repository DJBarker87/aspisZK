use super::*;
#[path="NDE_reference.rs"] pub(super) mod reference;
pub(super) fn to_ref(v:QM31)->reference::Q { reference::Q { c0:reference::C{a:v.c0.a.0,b:v.c0.b.0},c1:reference::C{a:v.c1.a.0,b:v.c1.b.0} } }
pub(super) fn to_native(v:reference::Q)->QM31 {QM31 {c0:CM31{a:M31(v.c0.a),b:M31(v.c0.b)},c1:CM31{a:M31(v.c1.a),b:M31(v.c1.b)}}}
#[kani::stub(core::ptr::copy_nonoverlapping, crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::extension_limbs)]
fn NDE_contract(){let v:[u32;4]=kani::any();let _=super::extension_limbs(to_native(reference::Q{c0:reference::C{a:v[0],b:v[1]},c1:reference::C{a:v[2],b:v[3]}}));}
#[kani::stub(core::ptr::copy_nonoverlapping, crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::extension_from_raw_limbs)]
fn NDE_raw_contract(){let v:[u64;4]=kani::any();kani::assume(v[0]<(1u64<<62)&&v[1]<(1u64<<62)&&v[2]<(1u64<<62)&&v[3]<(1u64<<62));let _=super::extension_from_raw_limbs(v); }
