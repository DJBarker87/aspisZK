use super::*;
#[path="NDD_reference.rs"] pub(super) mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub(super) fn verdict(v:bool)->bool{if cfg!(NDD_negative_guard){!v}else{v}}
fn q()->K{let x:[u32;4]=kani::any();K{c0:aspis_core::field::CM31{a:M31(x[0]),b:M31(x[1])},c1:aspis_core::field::CM31{a:M31(x[2]),b:M31(x[3])}}}
#[kani::proof_for_contract(shared_two_point_guard)] #[kani::unwind(12)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn guard_contract(){let w=Weights{variant:match kani::any::<u8>()%3{0=>Variant::S1,1=>Variant::S2,_=>Variant::D},
factors:core::array::from_fn(|_|core::array::from_fn(|_|core::array::from_fn(|_|q()))),
points:core::array::from_fn(|_|core::array::from_fn(|_|q())),extra:core::array::from_fn(|_|q())};
shared_two_point_guard(&w,kani::any());}
