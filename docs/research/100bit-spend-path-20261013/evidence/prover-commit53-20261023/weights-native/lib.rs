#![allow(unexpected_cfgs)]
use std::{boxed::Box,vec::Vec,mem::MaybeUninit};
#[derive(Clone,Copy)] pub struct M31(pub u32);
#[derive(Clone,Copy)] pub struct CM31 {pub a:M31,pub b:M31}
#[derive(Clone,Copy)] pub struct QM31 {pub c0:CM31,pub c1:CM31}
type K=QM31;
#[derive(Clone,Copy)] pub enum Variant {S1,S2,D}
struct Weights {variant:Variant,factors:[[[K;4];5];5],points:[[K;10];3],extra:[K;2]}
fn uninit<T>()->Result<Box<MaybeUninit<T>>,()> {
 let mut out=Vec::<MaybeUninit<T>>::new();
 out.try_reserve_exact(1).map_err(|_|())?;
 unsafe {out.set_len(1);}
 let ptr=Box::into_raw(out.into_boxed_slice()) as *mut MaybeUninit<T>;
 Ok(unsafe {Box::from_raw(ptr)})
}
// The native allocation/write cut after successful point/row producers.
// Arithmetic row answers are universally supplied, not asserted correct here.
fn stored(variant:Variant,alpha:[K;10],points:[[K;10];3],rows:[[[K;4];5];5])->Result<Box<Weights>,()> {
 let mut out=uninit::<Weights>()?;
 unsafe {
  let p=out.as_mut_ptr();
  core::ptr::addr_of_mut!((*p).variant).write(variant);
  core::ptr::addr_of_mut!((*p).points).write(points);
  core::ptr::addr_of_mut!((*p).extra).write([alpha[8],alpha[9]]);
  for k in 0..3 {for d in 0..5 {(*p).factors[k][d]=rows[k][d];}}
  for k in 0..2 {
   (*p).factors[3+k][0]=rows[3+k][0];
   for d in 1..5 {(*p).factors[3+k][d]=rows[3+k][d];}
  }
  Ok(out.assume_init())
 }
}
fn q(x:[u32;4])->K {K{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn limb(x:K,i:usize)->u32 {match i {0=>x.c0.a.0,1=>x.c0.b.0,2=>x.c1.a.0,_=>x.c1.b.0}}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(12)] fn initialized_weights_storage() {
  let alpha:[K;10]=kani::any::<[[u32;4];10]>().map(q);
  let points:[[K;10];3]=kani::any::<[[[u32;4];10];3]>().map(|p|p.map(q));
  let rows:[[[K;4];5];5]=kani::any::<[[[[u32;4];4];5];5]>().map(|m|m.map(|r|r.map(q)));
  let variant=if kani::any() {Variant::S1}else if kani::any() {Variant::S2}else{Variant::D};
  let result=stored(variant,alpha,points,rows);
  // Native source explicitly returns Allocation on reserve failure.
  if let Ok(out)=result {
   let k:usize=kani::any();kani::assume(k<5);
   let d:usize=kani::any();kani::assume(d<5);
   let r:usize=kani::any();kani::assume(r<4);
   let i:usize=kani::any();kani::assume(i<4);
   let p:usize=kani::any();kani::assume(p<3);
   let c:usize=kani::any();kani::assume(c<10);
   let e:usize=kani::any();kani::assume(e<2);
   assert_eq!(limb(out.factors[k][d][r],i),limb(rows[k][d][r],i));
   assert_eq!(limb(out.points[p][c],i),limb(points[p][c],i));
   assert_eq!(limb(out.extra[e],i),limb(alpha[8+e],i));
   assert_eq!(out.variant as u8,variant as u8);
  }
 }
}
