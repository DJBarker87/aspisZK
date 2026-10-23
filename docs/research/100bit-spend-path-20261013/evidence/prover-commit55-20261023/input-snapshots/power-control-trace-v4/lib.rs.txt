#![allow(dead_code,unexpected_cfgs)]
// Operations are open calls. This gate compares their arguments, order and
// returned-state use; their concrete canonical arithmetic is proved in Lean.
fn native_step<T:Copy>(mut base:T,mut exp:u64,mut acc:T,mut op:impl FnMut(u8,T,T)->T)->(T,u64,T) {
 if exp>0 {
  if exp&1==1 {acc=op(0,acc,base);}
  base=op(1,base,base);exp>>=1;
 }
 (base,exp,acc)
}
fn owned_step<T:Copy>(base:T,exp:u64,acc:T,mut op:impl FnMut(u8,T,T)->T)->(T,u64,T) {
 if exp==0 {(base,exp,acc)} else {
  let next=if exp&1==1 {op(0,acc,base)} else {acc};
  (op(1,base,base),exp>>1u32,next)
 }
}
#[cfg(kani)] mod proof {
 use super::*;
 #[kani::proof] #[kani::unwind(35)] fn power_control_trace() {
  let base:[u32;2]=kani::any();let acc:[u32;2]=kani::any();let exp:u64=kani::any();
  let values:[[u32;2];2]=kani::any();let mut a=[[0u32;5];2];let mut b=a;let mut na=0;let mut nb=0;
  let native=native_step(base,exp,acc,|op,x,y| {a[na]=[op as u32,x[0],x[1],y[0],y[1]];na+=1;values[op as usize]});
  let owned=owned_step(base,exp,acc,|op,x,y| {b[nb]=[op as u32,x[0],x[1],y[0],y[1]];nb+=1;values[op as usize]});
  assert_eq!(native,owned);assert_eq!(na,nb);
  let i:u8=kani::any();kani::assume(i<2);assert_eq!(a[i as usize],b[i as usize]);
 }
}
