use super::*;
// Natural-number field specs paired with emitted-definition theorems.
pub(super) fn neg_ref(x:u32)->u32{if x==0{0}else{2147483647-x}}
pub(super) fn cm_ref(x:u32)->(u32,u32){(x,0)}
pub(super) fn qm_ref(a:u32,b:u32)->(u32,u32,u32,u32){(a,b,0,0)}
#[kani::proof_for_contract(M31::neg)]
fn neg_contract(){let x=M31(kani::any());kani::assume(x.0<P);let _=x.neg();}
#[kani::proof_for_contract(CM31::from_m31)]
fn cm_contract(){let _=CM31::from_m31(M31(kani::any()));}
#[kani::proof_for_contract(QM31::from_cm31)]
fn qm_contract(){let _=QM31::from_cm31(CM31{a:M31(kani::any()),b:M31(kani::any())});}
