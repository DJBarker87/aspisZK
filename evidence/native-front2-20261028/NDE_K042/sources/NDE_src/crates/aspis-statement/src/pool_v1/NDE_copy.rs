use super::*;
#[path="NDE_reference.rs"] pub(super) mod reference;
pub(super) fn to_ref(v:QM31)->reference::Q { reference::Q { c0:reference::C{a:v.c0.a.0,b:v.c0.b.0},c1:reference::C{a:v.c1.a.0,b:v.c1.b.0} } }
pub(super) fn to_native(v:reference::Q)->QM31 {QM31 {c0:CM31{a:M31(v.c0.a),b:M31(v.c0.b)},c1:CM31{a:M31(v.c1.a),b:M31(v.c1.b)}}}
#[kani::stub(core::ptr::copy_nonoverlapping, crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::lift_m31)]
fn NDE_contract(){let v:u32=kani::any();let _=super::lift_m31(M31(v));}
fn row_canonical(q:QM31)->bool{q.c0.a.0<0x7fff_ffff&&q.c0.b.0<0x7fff_ffff&&q.c1.a.0<0x7fff_ffff&&q.c1.b.0<0x7fff_ffff}
#[kani::proof]
#[kani::unwind(66)]
#[kani::stub(aspis_core::field::QM31::mul,crate::NDE_field::qm31)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
fn NDE_row(){
 let h:[[u32;4];64]=kani::any();let l:[[u32;4];16]=kani::any();
 let conv=|a:[u32;4]|to_native(reference::Q{c0:reference::C{a:a[0],b:a[1]},c1:reference::C{a:a[2],b:a[3]}});
 let selectors=Selectors{high:h.map(conv),low:l.map(conv)};
 let row:usize=kani::any();kani::assume(row<1024);
 let (left,right)=reference::row_operands_ref(&selectors.high,&selectors.low,row);
 kani::assume(row_canonical(left)&&row_canonical(right));
 unsafe{crate::NDE_field::NDE_COUNT=0;}
 let result=selectors.row(row);
 let ok=unsafe{crate::NDE_field::NDE_COUNT==1&&crate::NDE_field::NDE_LEFT==left&&crate::NDE_field::NDE_RIGHT==right&&crate::NDE_field::NDE_REPLY==result};
 assert!(ok != cfg!(NDE_invert));
}
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::link_weight)]
fn NDE_link(){let k:u8=kani::any();let l:u8=kani::any();kani::assume(k<=4&&(k<3||l<64));let i:u64=kani::any();let v=if kani::any(){PoolV1PairForestCompiledVariantV1::Withdrawal}else{PoolV1PairForestCompiledVariantV1::PrivateTransfer};let ep=CompiledPoolV1PairForestEndpoint{row:kani::any(),slot:kani::any(),pattern:kani::any()};let link=CompiledPoolV1PairForestLink{tag:kani::any(),weight_kind:k,weight_level:l,producer:ep,consumer:CompiledPoolV1PairForestEndpoint{row:kani::any(),slot:kani::any(),pattern:kani::any()}};let _=super::link_weight(link,i,v); }
