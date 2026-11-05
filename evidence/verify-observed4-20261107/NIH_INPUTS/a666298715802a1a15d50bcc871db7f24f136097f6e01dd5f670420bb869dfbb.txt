use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_lift(){
 let raw:u32=kani::any();let out=lift_m31(M31(raw));
 let i:usize=kani::any();kani::assume(i<4);
 let got=[out.c0.a.0,out.c0.b.0,out.c1.a.0,out.c1.b.0][i];
 assert_eq!(got,(if i==0{raw}else{0}) ^ if cfg!(NIH_invert){1}else{0});
}

fn NIH_words(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn NIH_q(w:[u32;4])->QM31{QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}}
#[kani::proof_for_contract(super::selected_binary_weight)]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_selected_binary(){
 let raw:[u32;4]=kani::any();let weight:u32=kani::any();let high=NIH_q(raw);
 let out=NIH_words(selected_binary_weight(high,M31(weight)));
 let j:usize=kani::any();kani::assume(j<4);
 assert_eq!(out[j],(if weight==1{raw[j]}else{0}));
}
#[kani::proof_for_contract(super::link_weight)]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NIH_link_weight(){
 let kind:u8=kani::any();let level:u8=kani::any();let append:u64=kani::any();let withdraw:bool=kani::any();
 kani::assume(kind<=4&&level<64);
 let variant=if withdraw{PoolV1PairForestCompiledVariantV1::Withdrawal}else{PoolV1PairForestCompiledVariantV1::PrivateTransfer};
 let endpoint=CompiledPoolV1PairForestEndpoint{row:kani::any(),slot:kani::any(),pattern:kani::any()};
 let link=CompiledPoolV1PairForestLink{tag:kani::any(),weight_kind:kind,weight_level:level,producer:endpoint,consumer:endpoint};
 let out=link_weight(link,append,variant).0;
 let bit=((append>>level)&1) as u32;
 let expected=match kind{0=>1,1=>(!withdraw) as u32,2=>withdraw as u32,3=>1-bit,4=>bit,_=>unreachable!()};
 assert!(out<=1);assert_eq!(out,expected);
}

pub(super) fn NIH_selected_ref(high:QM31,weight:M31)->QM31{if weight.0==1{high}else{QM31::ZERO}}
pub(super) fn NIH_link_ref(kind:u8,level:u8,index:u64,withdraw:bool)->u32{
 match kind{0=>1,1=>if withdraw{0}else{1},2=>if withdraw{1}else{0},3=>1-((index>>level)&1) as u32,4=>((index>>level)&1) as u32,_=>panic!("invalid link weight")}
}
