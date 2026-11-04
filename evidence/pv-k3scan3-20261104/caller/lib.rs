#![feature(allocator_api)]
extern crate alloc;
use aspis_core::field::{QM31,CM31,M31};
mod host; mod reference;
fn q()->QM31 {let x:[u32;4]=kani::any(); QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn qs<const N:usize>()->[QM31;N] {let mut a=[QM31::ZERO;N];let mut i=0;while i<N {a[i]=q();i+=1;}a}
fn check(a:QM31,b:QM31) {if cfg!(feature="negative-control") {assert_ne!(a,b);}else{assert_eq!(a,b);}}
mod equivalence17 {
 use super::*;
 #[kani::proof] #[kani::unwind(256)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
 fn sum_high_nodes() {let h=qs();let l=qs();let ranges=[4..25,33..57];if cfg!(feature="context") {crate::context::check(h,l,&ranges);} else {let mut log=();let a=caller(h,l,&ranges,&mut log);check(a,reference::sum(h,l,&ranges));}}
 #[kani::proof] #[kani::unwind(256)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
 fn sum_high_path() {let h=qs();let l=qs();let ranges=[57..63];if cfg!(feature="context") {crate::context::check(h,l,&ranges);} else {let mut log=();let a=caller(h,l,&ranges,&mut log);check(a,reference::sum(h,l,&ranges));}}
 // No mul/square child is reached by this frozen cone. Empty modifies/effect set.
 fn caller(h:[QM31;64],l:[QM31;16],r:&[core::ops::Range<usize>],_log:&mut ())->QM31 {host::sum(h,l,r)}
}

include!("array.rs");

mod shared_callee16;
mod equivalence16 {
 use super::*;
 #[kani::proof] #[kani::unwind(128)]
 #[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
 fn shared_repeat16() {
  if cfg!(feature="context") {crate::repeat_context::caller();return;}
  let mut log=shared_callee16::Memo::new();
  shared_callee16::roundtrip16(&mut log);
  let a=q();let b=q();
  let x=shared_callee16::mul(a,b,&mut log);
  let y=shared_callee16::mul(a,b,&mut log);
  if cfg!(feature="negative-control") {
   let mode=crate::mutation();let limb=mode%4;
   let target=if mode<4 {&mut log.output[0]}else if mode<8 {&mut log.left[0]}else {&mut log.right[0]};
   match limb {0=>target.c0.a.0^=1,1=>target.c0.b.0^=1,2=>target.c1.a.0^=1,_=>target.c1.b.0^=1};
  }
  assert_eq!(x,y);
  assert_eq!(log.used,1);assert_eq!(log.tag[0],0);
  assert_eq!(log.left[0],a);assert_eq!(log.right[0],b);assert_eq!(log.output[0],x);
 }
}

#[path="default.rs"] mod generic_default_gate;

#[allow(non_snake_case)] mod KMX_stubs;

mod context;

fn mutation()->usize {
 if cfg!(feature="mutation-0") {return 0;}
 if cfg!(feature="mutation-1") {return 1;}
 if cfg!(feature="mutation-2") {return 2;}
 if cfg!(feature="mutation-3") {return 3;}
 if cfg!(feature="mutation-4") {return 4;}
 if cfg!(feature="mutation-5") {return 5;}
 if cfg!(feature="mutation-6") {return 6;}
 if cfg!(feature="mutation-7") {return 7;}
 if cfg!(feature="mutation-8") {return 8;}
 if cfg!(feature="mutation-9") {return 9;}
 if cfg!(feature="mutation-10") {return 10;}
 if cfg!(feature="mutation-11") {return 11;}
 0
}

mod repeat_context;
