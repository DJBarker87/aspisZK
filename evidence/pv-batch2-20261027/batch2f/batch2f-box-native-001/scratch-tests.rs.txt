#[cfg(test)]
mod pv_b2_box_boundary {
 extern crate std;
 use super::*;
 use std::alloc::{GlobalAlloc,Layout,System};
 use std::cell::Cell;
 use aspis_core::field::{CM31,M31,P};
 std::thread_local! {
  static ACTIVE:Cell<bool>=const{Cell::new(false)};
  static COUNTS:Cell<(usize,usize,usize,usize)>=const{Cell::new((0,0,0,0))};
 }
 struct Audit;
 fn note(layout:Layout,free:bool) {
  if layout.size()!=core::mem::size_of::<Weights>() || layout.align()!=core::mem::align_of::<Weights>() {return;}
  let active=ACTIVE.try_with(|x|x.get()).unwrap_or(false);
  if active {let _=COUNTS.try_with(|x|{let (a,d,b,f)=x.get();x.set(if free{(a,d+1,b,f+layout.size())}else{(a+1,d,b+layout.size(),f)});});}
 }
 unsafe impl GlobalAlloc for Audit {
  unsafe fn alloc(&self,l:Layout)->*mut u8 {note(l,false);unsafe{System.alloc(l)}}
  unsafe fn dealloc(&self,p:*mut u8,l:Layout){note(l,true);unsafe{System.dealloc(p,l)}}
 }
 #[global_allocator] static ALLOCATOR:Audit=Audit;
 fn measure(f:impl FnOnce())->(usize,usize,usize,usize) {
  COUNTS.with(|x|x.set((0,0,0,0)));ACTIVE.with(|x|x.set(true));
  f();ACTIVE.with(|x|x.set(false));COUNTS.with(|x|x.get())
 }
 #[test]
 fn actual_factory_layout_allocation_drop_and_values() {
  assert!(!cfg!(debug_assertions));
  assert_eq!(core::mem::size_of::<Weights>(),core::mem::size_of::<crate::weights::Weights>());
  assert_eq!(core::mem::align_of::<Weights>(),core::mem::align_of::<crate::weights::Weights>());
  let raw=K{c0:CM31{a:M31(u32::MAX),b:M31(P)},c1:CM31{a:M31(P+1),b:M31(P-1)}};
  let z=[SecureCirclePoint{x:K::ONE,y:K::ZERO};2];let mut pairs=0usize;
  for alpha in [[K::ZERO;10],[K::ONE;10],[raw;10]] {
   for variant in [Variant::S1,Variant::S2,Variant::D] {
    let original=measure(||{
     let x=std::hint::black_box(crate::weights::Weights::new(variant,&alpha,&z).unwrap());
     std::hint::black_box(&*x);drop(x);
    });
    let copied=measure(||{
     let x=std::hint::black_box(crate::prover::retain_weights_box(Weights::new(variant,&alpha,&z).unwrap()));
     std::hint::black_box(&*x);drop(x);
    });
    assert_eq!(copied,original);assert_eq!((copied.0,copied.1),(1,1));
    assert_eq!(copied.2,core::mem::size_of::<Weights>());assert_eq!(copied.2,copied.3);
    let a=crate::prover::retain_weights_box(Weights::new(variant,&alpha,&z).unwrap());
    let b=crate::weights::Weights::new(variant,&alpha,&z).unwrap();
    assert_eq!(a.factors,b.factors);assert_eq!(a.points,b.points);assert_eq!(a.extra,b.extra);
    for kind in 0..7 {for j in 0..1024 {assert_eq!(a.raw(kind,j),b.raw(kind,j));}}
    let kappa=E::from_limbs([2,3,4,5,6,7,8,9]).unwrap();let mut out=[E::ONE;1024];
    a.materialize(kappa,&mut out).unwrap();let expected=b.materialize(kappa).unwrap();
    assert_eq!(out.as_slice(),expected.as_slice());pairs+=1;
    std::println!("BOX_PAIR {:?} alloc_drop_bytes={:?}",variant,copied);
   }
  }
  std::println!("BOX_NATIVE_OK pairs={} raw_cells={} materialized_cells={} size={} align={}",pairs,pairs*7*1024,pairs*1024,core::mem::size_of::<Weights>(),core::mem::align_of::<Weights>());
 }
}
