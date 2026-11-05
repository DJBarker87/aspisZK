pub(super) fn NHU_ref_i(value:CM31)->CM31{CM31{a:M31(if value.b.0==0{0}else{P-value.b.0}),b:value.a}}
pub(super) fn NHU_ref_r(value:CM31)->CM31{CM31{a:M31(sub(add(value.a.0,value.a.0),value.b.0)),b:M31(add(value.a.0,add(value.b.0,value.b.0)))}}
pub(super) fn NHU_ref_tower(value:QM31,coordinate:usize)->QM31{match coordinate{0=>value,1=>QM31{c0:NHU_ref_i(value.c0),c1:NHU_ref_i(value.c1)},2=>QM31{c0:NHU_ref_r(value.c1),c1:value.c0},_=>QM31{c0:NHU_ref_i(NHU_ref_r(value.c1)),c1:NHU_ref_i(value.c0)}}}
#[kani::proof_for_contract(cm31_mul_i)]#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_contract_i(){let _=cm31_mul_i(canonical_cm());}
#[kani::proof_for_contract(cm31_mul_r)]#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_contract_r(){let _=cm31_mul_r(canonical_cm());}
#[kani::proof_for_contract(mul_tower_basis)]#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_contract_tower(){let coordinate:usize=kani::any();kani::assume(coordinate<4);let _=mul_tower_basis(canonical_q(),coordinate);}
