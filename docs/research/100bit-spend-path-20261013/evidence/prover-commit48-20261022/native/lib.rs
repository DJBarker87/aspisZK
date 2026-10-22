#![allow(dead_code,unexpected_cfgs)]
// Trace-parametric callee abstraction: answers are universal symbolic inputs,
// not a replacement field. Both executions consume the same answer sequence;
// every argument and operation is compared before reusing the field proofs.
#[repr(transparent)]
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct E(u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct Call {op:u8,a:E,b:E}
const EMPTY:Call=Call{op:0,a:E(0),b:E(0)};
static mut ANSWERS:[u32;8]=[0;8];
static mut CALLS:[Call;8]=[EMPTY;8];
static mut NEXT:usize=0;
fn reset(answers:[u32;8]) {unsafe {ANSWERS=answers;CALLS=[EMPTY;8];NEXT=0;}}
fn call(op:u8,a:E,b:E)->E {unsafe {
 let i=NEXT;assert!(i<8);CALLS[i]=Call{op,a,b};NEXT+=1;E(ANSWERS[i])
}}
fn trace()->([Call;8],usize) {unsafe {(CALLS,NEXT)}}
impl E {
 const ONE:Self=E(1);
 fn add(self,b:E)->E {call(1,self,b)}
 fn mul(self,b:E)->E {call(2,self,b)}
 fn sub(self,b:E)->E {call(3,self,b)}
}
include!("iterations.rs");
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(1026)]
 fn pair_iteration() {
  let raw:[u32;1024]=kani::any();let q:[E;1024]=unsafe {core::mem::transmute(raw)};
  let raw:[u32;512]=kani::any();let basis:[E;512]=unsafe {core::mem::transmute(raw)};
  let i:usize=kani::any();kani::assume(i<512);
  let p0=E(kani::any());let p1=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_pair(&q,basis,i,p0,p1);let ta=trace();
  reset(answers);let b=owner_pair(q,basis,i,p0,p1);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,4);
 }
 #[kani::proof] #[kani::unwind(514)]
 fn basis_fill_iteration() {
  let raw:[u32;512]=kani::any();let out=raw.map(E);
  let width:usize=kani::any();let j:usize=kani::any();
  kani::assume(width>0 && width<=256 && j<width);
  let factor=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_fill(out,width,j,factor);let ta=trace();
  reset(answers);let b=owner_fill(out,width,j,factor);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,1);
 }
 #[kani::proof] #[kani::unwind(10)]
 fn basis_stage_iteration() {
  let width:usize=kani::any();kani::assume(width>0 && width<=256);
  let factor=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_stage(width,factor);let ta=trace();
  reset(answers);let b=owner_stage(width,factor);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,3);
 }
}
include!("opening-iterations.rs");
include!("powers-iterations.rs");
include!("extra-iterations.rs");
include!("interpolate-iterations.rs");
include!("interpolate-outer.rs");
