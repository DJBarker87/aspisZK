use super::*;
#[path="NDD_reference.rs"] pub(super) mod reference;
pub(super) fn verdict(v:bool)->bool {if cfg!(NDD_negative){!v}else{v}}
pub(super) fn limbs(x:QM31)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
pub(super) fn qm(x:[u32;4])->QM31{QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
pub(super) fn canonical(x:QM31)->bool{let x=limbs(x);x[0]<P && x[1]<P && x[2]<P && x[3]<P}
pub(super) fn prepared_limbs(x:PreparedQm31Multiplier)->[u32;9]{let a=x.components;[a[0][0].0,a[0][1].0,a[0][2].0,a[1][0].0,a[1][1].0,a[1][2].0,a[2][0].0,a[2][1].0,a[2][2].0]}
#[kani::proof_for_contract(M31::reduce_u62)] fn reduce_contract(){M31::reduce_u62(kani::any());}
#[kani::proof_for_contract(PreparedQm31Multiplier::new)] fn prepared_contract(){PreparedQm31Multiplier::new(qm(kani::any()));}
#[kani::proof_for_contract(CM31::from_m31)] fn from_contract(){CM31::from_m31(M31(kani::any()));}
#[kani::proof_for_contract(M31::neg)] fn mneg_contract(){M31(kani::any()).neg();}
#[kani::proof_for_contract(CM31::neg)] fn cneg_contract(){CM31{a:M31(kani::any()),b:M31(kani::any())}.neg();}
#[kani::proof_for_contract(QM31::neg)] fn qneg_contract(){qm(kani::any()).neg();}
#[kani::proof_for_contract(QM31::is_zero)] fn zero_contract(){qm(kani::any()).is_zero();}
