use super::*;
#[path="NFQ_reference.rs"] pub(super) mod reference;
pub(super) fn code(v:Variant)->u8{match v {Variant::S1=>0,Variant::S2=>1,Variant::D=>2}}
fn variant()->Variant{match kani::any::<u8>()%3 {0=>Variant::S1,1=>Variant::S2,_=>Variant::D}}
#[kani::proof_for_contract(Variant::folds)]
fn folds_contract(){let _=variant().folds();}
#[kani::proof_for_contract(Variant::final_len)]
fn final_len_contract(){let _=variant().final_len();}
