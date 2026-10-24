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
static mut POWERS_COUNT:usize=0;
static mut POWERS_INPUT:[u32;8]=[0;8];
static mut POWERS_OUTPUT:[[u32;8];7]=[[0;8];7];
// Whole verified powers callee is a common normal-return child. All returned
// words remain arbitrary; no arithmetic, canonicality or success is assumed.
fn powers_leaf<const N:usize>(seed:E)->[E;N] {
 assert_eq!(N,7);
 let input:[u32;8]=unsafe{core::mem::transmute(seed)};
 unsafe {
   assert!(POWERS_COUNT<2);
   if POWERS_COUNT==0{POWERS_INPUT=input;}else{assert_eq!(input,POWERS_INPUT);}
   POWERS_COUNT+=1;
   let result:[E;7]=core::mem::transmute(POWERS_OUTPUT);
   core::mem::transmute_copy(&result)
 }
}
#[kani::proof]
#[kani::stub(aspis_r1_cost_probe::weights::powers,powers_leaf)]
#[kani::unwind(128)]
#[kani::stub(fast_pairing::EbyKDot::push,push_leaf)]
#[kani::stub(fast_pairing::EbyKDot::finish,finish_leaf)]
#[kani::stub(aspis_r1_cost_probe::weights::field,field_leaf)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::mul,mul_leaf)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::add,add_leaf)]
fn original_claim_with_common_powers_matches_reference() {
 assert!(!core::mem::needs_drop::<EbyKDot>());
 let sem=semantic(kani::any(),kani::any(),kani::any());
 let values:[[u32;8];29]=kani::any();let g:[E;29]=unsafe{core::mem::transmute(values)};
 let y1:[u8;928]=kani::any();let inactive:[u32;8]=kani::any();let kappa:[u32;8]=kani::any();
 let inactive:E=unsafe{core::mem::transmute(inactive)};let kappa:E=unsafe{core::mem::transmute(kappa)};
 unsafe{POWERS_COUNT=0;POWERS_OUTPUT=kani::any();}
 let a=prepared_claim(&sem,&y1,inactive,&g,kappa);
 let b=prepared_claim_owned(&sem,&y1,inactive,&g,kappa);
 assert_eq!(a,b);assert_eq!(unsafe{POWERS_COUNT},2);
 kani::cover!(a.is_ok(),"whole original/reference returns Ok");
 kani::cover!(a.is_err(),"whole original/reference returns Err");
}
