#![allow(static_mut_refs)]
use super::*;
use alloc::boxed::Box;
use aspis_core::field::{M31,CM31};
use fast_pairing::{EbyKDot,ProofQ};
#[derive(Clone,Copy)] struct Hash;
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{panic!("Digest32 must be unused in claim scope")}}
fn semantic(claims:[[[u32;4];29];3],extra:[[u32;4];29],before:[[u32;4];29])->r1_semantic::Verified<Hash> {
 use aspis_r1_cost_probe::r1_wire::{Challenges,SemanticTranscript};
 use aspis_core::circle::SecureCirclePoint;
 r1_semantic::Verified {
 roots:kani::any(),challenges:unsafe{core::mem::transmute(kani::any::<[u32;{core::mem::size_of::<Challenges>()/4}]>())},
 alpha:unsafe{core::mem::transmute(kani::any::<[[u32;4];10]>())},claims:Box::new(unsafe{core::mem::transmute(claims)}),extra:unsafe{core::mem::transmute(extra)},before_z1:unsafe{core::mem::transmute(before)},state_before_z0:kani::any(),
 z:unsafe{core::mem::transmute(kani::any::<[[u32;8];2]>())},transcript:SemanticTranscript::proof_input(Hash,kani::any(),kani::any()),
 }
}
extern "C" {
 fn aspis_uf_push(input:*const u64,output:*mut u64)->u32;
 fn aspis_uf_raw(input:*const u32,output:*mut u64)->u32;
 fn aspis_uf_finish(input:*const u64,output:*mut u32)->u32;
 fn aspis_uf_field(input:*const u32,output:*mut u32)->u32;
 fn aspis_uf_mul(input:*const u32,output:*mut u32)->u32;
 fn aspis_uf_add(input:*const u32,output:*mut u32)->u32;
}
fn raw_words(a:[u32;4],b:[u32;4])->[u64;4] {
 let input=[a[0],a[1],a[2],a[3],b[0],b[1],b[2],b[3]];
 let mut output=[0;4];unsafe{assert_eq!(aspis_uf_raw(input.as_ptr(),output.as_mut_ptr()),0);}output
}
fn raw_leaf(a:ProofQ,b:ProofQ)->[u64;4] {raw_words(a.limbs(),b.limbs())}
fn field_leaf(bytes:&[u8],index:usize)->E {
 let offset=index*32;let frame=&bytes[offset..offset+32];
 let mut input=[0u32;8];
 for j in 0..8 {input[j]=u32::from_le_bytes([frame[j*4],frame[j*4+1],frame[j*4+2],frame[j*4+3]]);}
 let mut output=[0u32;8];unsafe{assert_eq!(aspis_uf_field(input.as_ptr(),output.as_mut_ptr()),0);core::mem::transmute(output)}
}
fn finish_leaf(dot:EbyKDot)->E {
 let input:[u64;9]=unsafe{core::mem::transmute(dot)};let mut output=[0u32;8];
 unsafe{assert_eq!(aspis_uf_finish(input.as_ptr(),output.as_mut_ptr()),0);core::mem::transmute(output)}
}
fn wide_input(a:E,b:E)->[u32;16] {
 let a:[u32;8]=unsafe{core::mem::transmute(a)};let b:[u32;8]=unsafe{core::mem::transmute(b)};
 [a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7],b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7]]
}
fn mul_leaf(a:E,b:E)->E {let input=wide_input(a,b);let mut output=[0u32;8];unsafe{assert_eq!(aspis_uf_mul(input.as_ptr(),output.as_mut_ptr()),0);core::mem::transmute(output)}}
fn add_leaf(a:E,b:E)->E {let input=wide_input(a,b);let mut output=[0u32;8];unsafe{assert_eq!(aspis_uf_add(input.as_ptr(),output.as_mut_ptr()),0);core::mem::transmute(output)}}
#[kani::proof]
#[kani::unwind(128)]
fn uf_congruence_preflight() {
 let a:[u32;4]=kani::any();let b:[u32;4]=kani::any();
 assert_eq!(raw_words(a,b),raw_words(a,b));
}
#[kani::proof]
#[kani::unwind(128)]
fn uf_last_input_negative_control() {
 let a:[u32;4]=kani::any();let b:[u32;4]=kani::any();let mut changed=b;changed[3]^=1;
 assert_eq!(raw_words(a,b),raw_words(a,changed));
}
#[kani::proof]
#[kani::unwind(128)]
#[kani::stub(fast_pairing::ProofQ::raw,raw_leaf)]
#[kani::stub(fast_pairing::EbyKDot::finish,finish_leaf)]
#[kani::stub(aspis_r1_cost_probe::weights::field,field_leaf)]
fn original_point_matches_fission() {
 let sem=semantic(kani::any(),kani::any(),kani::any());
 let point:usize=kani::any();kani::assume(point<6);
 let coeffs:[[u32;8];29]=kani::any();let g:[E;29]=unsafe{core::mem::transmute(coeffs)};
 let parts:[[u32;8];7]=kani::any();let initial:[E;7]=unsafe{core::mem::transmute(parts)};
 let mut old=initial;let mut new=initial;let y1:[u8;928]=kani::any();
 let a=original_point_step(&sem,&y1,&g,point,&mut old);
 let b=reference_point_step(&sem,&y1,&g,point,&mut new);
 assert_eq!(a,b);assert_eq!(old,new);
 if a.is_err(){assert!(matches!(a,Err(Error::Parse)));assert_eq!(old,initial);}
 kani::cover!(a.is_ok(),"all29 pushes and parts update");kani::cover!(a.is_err(),"early rejection");
 kani::cover!(a.is_ok()&&point==5,"y1 point completes");kani::cover!(a.is_err()&&point==5,"y1 scalar rejected");
}
#[kani::proof]
#[kani::unwind(128)]
#[kani::stub(fast_pairing::ProofQ::raw,raw_leaf)]
#[kani::stub(fast_pairing::EbyKDot::finish,finish_leaf)]
#[kani::stub(aspis_r1_cost_probe::weights::field,field_leaf)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::mul,mul_leaf)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::add,add_leaf)]
fn original_claim_matches_fission() {
 let sem=semantic(kani::any(),kani::any(),kani::any());
 let coeffs:[[u32;8];29]=kani::any();let g:[E;29]=unsafe{core::mem::transmute(coeffs)};
 let y1:[u8;928]=kani::any();let inactive:[u32;8]=kani::any();let kappa:[u32;8]=kani::any();
 let inactive:E=unsafe{core::mem::transmute(inactive)};let kappa:E=unsafe{core::mem::transmute(kappa)};
 let a=prepared_claim(&sem,&y1,inactive,&g,kappa);let b=fission_claim(&sem,&y1,inactive,&g,kappa);
 assert_eq!(a,b);kani::cover!(a.is_ok(),"whole claim returns Ok");kani::cover!(a.is_err(),"whole claim returns Err");
}

fn push_words(state:[u64;9],value:[u32;8],scalar:[u32;4])->[u64;10] {
 let input=[state[0],state[1],state[2],state[3],state[4],state[5],state[6],state[7],state[8],
 u64::from(value[0]),u64::from(value[1]),u64::from(value[2]),u64::from(value[3]),u64::from(value[4]),u64::from(value[5]),u64::from(value[6]),u64::from(value[7]),
 u64::from(scalar[0]),u64::from(scalar[1]),u64::from(scalar[2]),u64::from(scalar[3])];
 let mut output=[0u64;10];unsafe{assert_eq!(aspis_uf_push(input.as_ptr(),output.as_mut_ptr()),0);}output
}
fn push_leaf(dot:&mut EbyKDot,value:E,scalar:K)->Result<(),()> {
 let state:[u64;9]=unsafe{core::mem::transmute_copy(&*dot)};
 let value:[u32;8]=unsafe{core::mem::transmute(value)};let scalar:[u32;4]=unsafe{core::mem::transmute(scalar)};
 let out=push_words(state,value,scalar);
 *dot=unsafe{core::mem::transmute([out[0],out[1],out[2],out[3],out[4],out[5],out[6],out[7],out[8]])};
 if out[9]&1!=0{Err(())}else{Ok(())}
}
#[kani::proof]
#[kani::unwind(128)]
fn uf_push_congruence_preflight() {
 let s:[u64;9]=kani::any();let v:[u32;8]=kani::any();let q:[u32;4]=kani::any();
 let a=push_words(s,v,q);let b=push_words(s,v,q);assert_eq!(a,b);
 kani::cover!(a[9]&1==0,"UF Ok");kani::cover!(a[9]&1!=0,"UF Err");
}
#[kani::proof]
#[kani::unwind(128)]
fn uf_push_last_input_negative() {
 let s:[u64;9]=kani::any();let v:[u32;8]=kani::any();let q:[u32;4]=kani::any();let mut changed=q;changed[3]^=1;
 assert_eq!(push_words(s,v,q),push_words(s,v,changed));
}
#[kani::proof]
#[kani::unwind(128)]
#[kani::stub(fast_pairing::EbyKDot::push,push_leaf)]
#[kani::stub(fast_pairing::EbyKDot::finish,finish_leaf)]
#[kani::stub(aspis_r1_cost_probe::weights::field,field_leaf)]
fn original_point_pure_push_matches_fission() {
 assert!(!core::mem::needs_drop::<EbyKDot>());assert!(!core::mem::needs_drop::<E>());
 let sem=semantic(kani::any(),kani::any(),kani::any());let point:usize=kani::any();kani::assume(point<6);
 let coeffs:[[u32;8];29]=kani::any();let g:[E;29]=unsafe{core::mem::transmute(coeffs)};
 let parts:[[u32;8];7]=kani::any();let initial:[E;7]=unsafe{core::mem::transmute(parts)};
 let mut old=initial;let mut new=initial;let y1:[u8;928]=kani::any();
 let a=original_point_step(&sem,&y1,&g,point,&mut old);let b=reference_point_step(&sem,&y1,&g,point,&mut new);
 assert_eq!(a,b);assert_eq!(old,new);
 if a.is_err(){assert!(matches!(a,Err(Error::Parse)));assert_eq!(old,initial);}
 kani::cover!(a.is_ok(),"29 arbitrary pushes then parts update");kani::cover!(a.is_err(),"arbitrary early rejection preserves parts");
}
#[kani::proof]
#[kani::unwind(128)]
#[kani::stub(fast_pairing::EbyKDot::push,push_leaf)]
#[kani::stub(fast_pairing::EbyKDot::finish,finish_leaf)]
#[kani::stub(aspis_r1_cost_probe::weights::field,field_leaf)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::mul,mul_leaf)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::add,add_leaf)]
fn original_claim_pure_push_matches_fission() {
 assert!(!core::mem::needs_drop::<EbyKDot>());
 let sem=semantic(kani::any(),kani::any(),kani::any());let coeffs:[[u32;8];29]=kani::any();let g:[E;29]=unsafe{core::mem::transmute(coeffs)};
 let y1:[u8;928]=kani::any();let inactive:[u32;8]=kani::any();let kappa:[u32;8]=kani::any();
 let inactive:E=unsafe{core::mem::transmute(inactive)};let kappa:E=unsafe{core::mem::transmute(kappa)};
 let a=prepared_claim(&sem,&y1,inactive,&g,kappa);let b=fission_claim(&sem,&y1,inactive,&g,kappa);
 assert_eq!(a,b);kani::cover!(a.is_ok(),"whole claim Ok");kani::cover!(a.is_err(),"whole claim Err");
}
