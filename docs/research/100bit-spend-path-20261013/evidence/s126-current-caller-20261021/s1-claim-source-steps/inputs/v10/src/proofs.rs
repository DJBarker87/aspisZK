use super::*;
use aspis_core::field::{M31,CM31};
use alloc::boxed::Box;
#[derive(Clone,Copy)] struct Hash;
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{[0;32]}}
fn qm(x:[u32;4])->K {K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn wide(x:[u32;8])->E {E::new(qm([x[0],x[1],x[2],x[3]]),qm([x[4],x[5],x[6],x[7]]))}
fn semantic(claims:[[[u32;4];29];3],extra:[[u32;4];29],before:[[u32;4];29])->r1_semantic::Verified<Hash> {
 use aspis_r1_cost_probe::r1_wire::{Challenges,SemanticTranscript};
 use aspis_core::circle::SecureCirclePoint;
 r1_semantic::Verified {
 roots:[[0;32];2],challenges:Challenges{lambda:K::ZERO,chi:K::ZERO,theta:K::ZERO,zc:core::array::from_fn(|_|K::ZERO),mu:K::ZERO,eta:K::ZERO},
 alpha:[K::ZERO;10],claims:Box::new(unsafe{core::mem::transmute(claims)}),extra:unsafe{core::mem::transmute(extra)},before_z1:unsafe{core::mem::transmute(before)},state_before_z0:[0;32],
 z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],transcript:SemanticTranscript::new(Hash,&[],&[0;32]).unwrap(),
 }
}
// Numeric-only full QM31/array representations are populated above by raw
// bit patterns to avoid proving unrelated array::map constructors. No reference,
// enum, Box or whole Verified object is transmuted.
// Arbitrary full integer accumulator representation; no enum/reference/drop
// fields. Size equality is checked by Rust's transmute type checker. Every
// bit pattern is valid. No field order is assumed or compared to a model.
fn dot_state(x:[u64;9])->fast_pairing::EbyKDot {unsafe{core::mem::transmute(x)}}
fn dot_image(x:fast_pairing::EbyKDot)->[u64;9] {unsafe{core::mem::transmute(x)}}
#[kani::proof]
#[kani::unwind(128)]
fn scalar_push_step_actual() {
 let sem=semantic(kani::any(),kani::any(),kani::any());
 let point:usize=kani::any();let l:usize=kani::any();kani::assume(point<5&&l<29);
 let coeffs:[[u32;8];29]=kani::any();let g:[E;29]=unsafe{core::mem::transmute(coeffs)};
 let state:[u64;9]=kani::any();let mut old=dot_state(state);let mut new=dot_state(state);
 let a=original_step(&sem,&[],&g,point,l,&mut old);
 let b=helper_step(&sem,&[],&g,point,l,&mut new);
 assert_eq!(a,b);assert_eq!(dot_image(old),dot_image(new));
 kani::cover!(a.is_ok(),"successful actual push");kani::cover!(a.is_err(),"rejected actual push");
}

#[kani::proof]
#[kani::unwind(128)]
fn scalar_selector_actual() {
 let sem=semantic(kani::any(),kani::any(),kani::any());
 let point:usize=kani::any();let l:usize=kani::any();kani::assume(point<5&&l<29);
 let original=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(&[],l).c0()};
 let helper=scalar_helper(&sem,&[],point,l);
 assert_eq!(original,helper);
 kani::cover!(point==0,"claims point zero");kani::cover!(point==1,"claims point one");kani::cover!(point==2,"claims point two");kani::cover!(point==3,"extra point");kani::cover!(point==4,"before_z1 point");
 kani::cover!(l==0,"first column");kani::cover!(l==28,"last column");
}

#[kani::proof]
#[kani::unwind(128)]
fn scalar_selector_y1_actual() {
 let sem=semantic([[[0;4];29];3],[[0;4];29],[[0;4];29]);
 let l:usize=kani::any();kani::assume(l<29);
 let digits:[u32;8]=kani::any();
 let mut bytes=[0u8;928];
 for j in 0..8 {
  kani::assume(digits[j]<0x7fff_ffff);
  bytes[l*32+j*4..l*32+(j+1)*4].copy_from_slice(&digits[j].to_le_bytes());
 }
 let original=field(&bytes,l).c0();
 let helper=scalar_helper(&sem,&bytes,5,l);
 assert_eq!(original,helper);
 kani::cover!(l==0,"first y1 frame");kani::cover!(l==28,"last y1 frame");
 kani::cover!(digits[0]==0,"zero first limb");kani::cover!(digits[0]==0x7fff_fffe,"maximum canonical first limb");
}

// Relational call-coupling certificate, not arithmetic evaluation. Both runs
// must present identical complete actual arguments to each leaf. Return and
// updated state are otherwise arbitrary shared values, including Err writes.
// This is an explicit external-call interpretation, not an actual push proof.
static mut PUSH_CALLS:usize=0;
static mut PUSH_INPUT:[u64;9]=[0;9];
static mut PUSH_VALUE:E=E::ZERO;
static mut PUSH_SCALAR:K=K::ZERO;
static mut PUSH_OUTPUT:[u64;9]=[0;9];
static mut PUSH_ERR:bool=false;
static mut FIELD_CALLS:usize=0;
static mut FIELD_PTR:*const u8=core::ptr::null();
static mut FIELD_LEN:usize=0;
static mut FIELD_INDEX:usize=0;
static mut FIELD_OUTPUT:E=E::ZERO;
fn coupled_field(bytes:&[u8],index:usize)->E {
 unsafe {
  if FIELD_CALLS==0 {FIELD_PTR=bytes.as_ptr();FIELD_LEN=bytes.len();FIELD_INDEX=index;}
  else {assert!(bytes.as_ptr()==FIELD_PTR);assert_eq!(bytes.len(),FIELD_LEN);assert_eq!(index,FIELD_INDEX);}
  FIELD_CALLS+=1;FIELD_OUTPUT
 }
}
fn coupled_push(dot:&mut fast_pairing::EbyKDot,value:E,scalar:K)->Result<(),()> {
 let input:[u64;9]=unsafe{core::mem::transmute_copy(&*dot)};
 unsafe {
  if PUSH_CALLS==0 {PUSH_INPUT=input;PUSH_VALUE=value;PUSH_SCALAR=scalar;}
  else {assert!(input==PUSH_INPUT);assert!(value==PUSH_VALUE);assert!(scalar==PUSH_SCALAR);}
  PUSH_CALLS+=1;*dot=dot_state(PUSH_OUTPUT);
  if PUSH_ERR {Err(())}else{Ok(())}
 }
}
#[kani::proof]
#[kani::unwind(128)]
#[kani::stub(fast_pairing::EbyKDot::push,coupled_push)]
#[kani::stub(aspis_r1_cost_probe::weights::field,coupled_field)]
fn scalar_push_step_coupled() {
 let sem=semantic(kani::any(),kani::any(),kani::any());
 let point:usize=kani::any();let l:usize=kani::any();kani::assume(point<6&&l<29);
 let coeffs:[[u32;8];29]=kani::any();let g:[E;29]=unsafe{core::mem::transmute(coeffs)};
 let y1:[u8;928]=kani::any();
 let state:[u64;9]=kani::any();let output:[u64;9]=kani::any();let error:bool=kani::any();
 let field:[u32;8]=kani::any();
 unsafe {PUSH_CALLS=0;FIELD_CALLS=0;PUSH_OUTPUT=output;PUSH_ERR=error;FIELD_OUTPUT=core::mem::transmute(field);}
 let mut old=dot_state(state);let mut new=dot_state(state);
 let a=original_step(&sem,&y1,&g,point,l,&mut old);
 let b=helper_step(&sem,&y1,&g,point,l,&mut new);
 assert_eq!(a,b);assert_eq!(dot_image(old),dot_image(new));
 assert_eq!(unsafe{PUSH_CALLS},2);assert_eq!(unsafe{FIELD_CALLS},if point==5 {2}else{0});
 assert_eq!(a,if error{Err(Error::Parse)}else{Ok(())});
 kani::cover!(error,"arbitrary error and mutated state");kani::cover!(!error,"arbitrary success and mutated state");
 kani::cover!(point==5&&l==28,"last y1 field/push call");
}

#[kani::proof]
#[kani::unwind(128)]
#[kani::stub(fast_pairing::EbyKDot::push,coupled_push)]
fn push_stub_result_preflight() {
 let error:bool=kani::any();let output:[u64;9]=kani::any();
 unsafe{PUSH_CALLS=0;PUSH_ERR=error;PUSH_OUTPUT=output;}
 let mut dot=dot_state([0;9]);
 let result=dot.push(E::ZERO,K::ZERO);
 assert_eq!(result,if error {Err(())}else{Ok(())});
 assert_eq!(dot_image(dot),output);
 assert_eq!(unsafe{PUSH_CALLS},1);
 kani::cover!(result.is_err(),"stub unit error returned");kani::cover!(result.is_ok(),"stub unit success returned");
}
