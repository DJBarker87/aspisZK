#![allow(static_mut_refs)]
use super::*;
use alloc::boxed::Box;
use aspis_core::field::{M31,CM31};
use fast_pairing::{EbyKDot,ProofQ};
#[derive(Clone,Copy)] struct Hash;
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{[0;32]}}
fn semantic(claims:[[[u32;4];29];3],extra:[[u32;4];29],before:[[u32;4];29])->r1_semantic::Verified<Hash> {
 use aspis_r1_cost_probe::r1_wire::{Challenges,SemanticTranscript};
 use aspis_core::circle::SecureCirclePoint;
 r1_semantic::Verified {
 roots:[[0;32];2],challenges:Challenges{lambda:K::ZERO,chi:K::ZERO,theta:K::ZERO,zc:core::array::from_fn(|_|K::ZERO),mu:K::ZERO,eta:K::ZERO},
 alpha:[K::ZERO;10],claims:Box::new(unsafe{core::mem::transmute(claims)}),extra:unsafe{core::mem::transmute(extra)},before_z1:unsafe{core::mem::transmute(before)},state_before_z0:[0;32],
 z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],transcript:SemanticTranscript::new(Hash,&[],&[0;32]).unwrap(),
 }
}
static mut SECOND:bool=false;
static mut RAW_COUNT:usize=0;
static mut RAW_SCRIPT:[[u64;4];58]=[[0;4];58];
static mut RAW_LEFT:[[u32;4];58]=[[0;4];58];
static mut RAW_RIGHT:[[u32;4];58]=[[0;4];58];
static mut FIELD_COUNT:usize=0;
static mut FIELD_SCRIPT:[E;29]=[E::ZERO;29];
static mut Y1_PTR:*const u8=core::ptr::null();
static mut Y1_LEN:usize=0;
static mut FINISH_COUNT:usize=0;
static mut FINISH_INPUT:[u64;9]=[0;9];
static mut FINISH_OUTPUT:E=E::ZERO;
fn raw_leaf(a:ProofQ,b:ProofQ)->[u64;4] {
 unsafe {
  let i=RAW_COUNT;assert!(i<58);
  if SECOND {assert_eq!(a.limbs(),RAW_LEFT[i]);assert_eq!(b.limbs(),RAW_RIGHT[i]);}
  else {RAW_LEFT[i]=a.limbs();RAW_RIGHT[i]=b.limbs();}
  RAW_COUNT=i+1;RAW_SCRIPT[i]
 }
}
fn field_leaf(bytes:&[u8],index:usize)->E {
 unsafe {
  assert_eq!(bytes.as_ptr(),Y1_PTR);assert_eq!(bytes.len(),Y1_LEN);
  assert_eq!(index,FIELD_COUNT);assert!(index<29);
  FIELD_COUNT+=1;FIELD_SCRIPT[index]
 }
}
fn finish_leaf(dot:EbyKDot)->E {
 let input:[u64;9]=unsafe{core::mem::transmute(dot)};
 unsafe {
  assert_eq!(FINISH_COUNT,0);
  if SECOND {assert_eq!(input,FINISH_INPUT);}else{FINISH_INPUT=input;}
  FINISH_COUNT=1;FINISH_OUTPUT
 }
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
 let fields:[[u32;8];29]=kani::any();let parts:[[u32;8];7]=kani::any();
 let initial:[E;7]=unsafe{core::mem::transmute(parts)};let mut old=initial;let mut new=initial;
 let y1:[u8;928]=kani::any();let raw:[[u64;4];58]=kani::any();let finish:[u32;8]=kani::any();
 unsafe {SECOND=false;RAW_COUNT=0;FIELD_COUNT=0;FINISH_COUNT=0;RAW_SCRIPT=raw;FIELD_SCRIPT=core::mem::transmute(fields);FINISH_OUTPUT=core::mem::transmute(finish);Y1_PTR=y1.as_ptr();Y1_LEN=y1.len();}
 let a=original_point_step(&sem,&y1,&g,point,&mut old);
 let raw_count=unsafe{RAW_COUNT};let field_count=unsafe{FIELD_COUNT};let finish_count=unsafe{FINISH_COUNT};
 unsafe {SECOND=true;RAW_COUNT=0;FIELD_COUNT=0;FINISH_COUNT=0;}
 let b=reference_point_step(&sem,&y1,&g,point,&mut new);
 assert_eq!(a,b);assert_eq!(old,new);
 assert_eq!(unsafe{RAW_COUNT},raw_count);assert_eq!(unsafe{FIELD_COUNT},field_count);assert_eq!(unsafe{FINISH_COUNT},finish_count);
 assert_eq!(finish_count,if a.is_ok(){1}else{0});
 if a.is_err(){assert!(matches!(a,Err(Error::Parse)));assert_eq!(old,initial);}
 kani::cover!(a.is_ok()&&raw_count==58,"29 actual pushes then finish");
 kani::cover!(a.is_err()&&raw_count==56,"last push rejects without parts update");
 kani::cover!(a.is_err()&&point==5,"y1 scalar rejection");
 kani::cover!(a.is_ok()&&point==5,"complete y1 point");
}
