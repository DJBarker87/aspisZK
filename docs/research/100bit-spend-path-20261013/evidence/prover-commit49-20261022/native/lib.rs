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
 fn mul_m31(self,b:M31)->E {call(4,self,E(b.0))}
 fn add(self,b:E)->E {call(1,self,b)}
 fn mul(self,b:E)->E {call(2,self,b)}
 fn sub(self,b:E)->E {call(3,self,b)}
}

#[derive(Clone,Copy)] struct M31(u32);
fn native_tail(mut point:[E;10],r:usize,remaining:usize,assignment:usize,offset:usize)->[E;10] {
 point[r+1+offset]=if (assignment>>(remaining-1-offset))&1==0 {E(0)} else {E::ONE};point
}
fn owner_tail(mut point:[E;10],round:usize,remaining:usize,assignment:usize,offset:usize)->[E;10] {
 point[round+1+offset]=if (assignment>>((remaining-1-offset) as u32))&1==0 {E(0)} else {E::ONE};point
}
fn native_sum(value:E,oracle:Result<E,u8>)->Result<E,u8> {Ok(value.add(oracle?))}
fn owner_sum(value:E,oracle:Result<E,u8>)->Result<E,u8> {match oracle {Err(e)=>Err(e),Ok(x)=>Ok(value.add(x))}}
fn native_shift(mut polys:[[E;28];10],original:E,eta:E,term0:E,inv:E,half:E)->[[E;28];10] {
 let c=original.sub(eta.mul(term0)).mul(inv);
 polys[9][0]=polys[9][0].sub(c.mul(half));
 polys[9][1]=polys[9][1].add(c);polys
}
fn owner_shift(mut p:[E;28],original:E,eta_term0:E,inv:E,half:E)->[E;28] {
 let c=original.sub(eta_term0).mul(inv);
 p[0]=p[0].sub(c.mul(half));
 p[1]=p[1].add(c);p
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(12)] fn tail_transition() {
  let raw:[u32;10]=kani::any();let p:[E;10]=unsafe {core::mem::transmute(raw)};
  let r:usize=kani::any();let n:usize=kani::any();let a:usize=kani::any();let o:usize=kani::any();
  kani::assume(r<10 && n==9-r && o<n && a<(1usize<<n));
  assert_eq!(native_tail(p,r,n,a,o),owner_tail(p,r,n,a,o));
 }
 #[kani::proof] #[kani::unwind(12)] fn oracle_sum_transition() {
  let v=E(kani::any());let x=E(kani::any());let err:u8=kani::any();let fail:bool=kani::any();
  let oracle=if fail {Err(err)}else{Ok(x)};let answers=kani::any();
  reset(answers);let a=native_sum(v,oracle);let ta=trace();
  reset(answers);let b=owner_sum(v,oracle);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,if fail {0}else{1});
 }
 #[kani::proof] #[kani::unwind(282)] fn final_shift() {
  let raw:[[u32;28];10]=kani::any();let p:[[E;28];10]=unsafe {core::mem::transmute(raw)};
  let original=E(kani::any());let eta=E(kani::any());let term0=E(kani::any());let inv=E(kani::any());let half=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_shift(p,original,eta,term0,inv,half);let ta=trace();
  reset(answers);let eta_term0=eta.mul(term0);let row=owner_shift(p[9],original,eta_term0,inv,half);let tb=trace();
  let mut b=p;b[9]=row;assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,6);
 }
}

include!("weights-iterations.rs");

include!("boundary-iterations.rs");
