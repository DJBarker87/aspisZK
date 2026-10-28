use super::*;
#[path="NDD_reference.rs"] pub(super) mod reference;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
pub(super) fn verdict(v:bool)->bool{if cfg!(NDD_negative_guard){!v}else{v}}
fn q()->K{let x:[u32;4]=kani::any();K{c0:aspis_core::field::CM31{a:M31(x[0]),b:M31(x[1])},c1:aspis_core::field::CM31{a:M31(x[2]),b:M31(x[3])}}}
#[kani::proof_for_contract(shared_two_point_guard)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn guard_contract(){let mut w=Weights{variant:if kani::any(){Variant::S2}else{Variant::S0},factors:[[[K::ZERO;4];5];5],points:[[K::ZERO;10];3],extra:[K::ZERO;2]};
// Only reached factors are arbitrary; all omitted fields are framed and unread.
let mut i=0;while i<4{w.factors[0][2][i]=q();w.factors[2][2][i]=q();w.factors[0][3][i]=q();w.factors[2][3][i]=q();i+=1;}
shared_two_point_guard(&w,kani::any());}
