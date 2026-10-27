#![no_std]
extern crate alloc;
#[path="../../NP6_claims/src/NP6_sampler.rs"]mod sampler;
#[path="../../NP6_claims/src/NP6_wire.rs"]mod r1_wire;
#[path="../../NP6_claims/src/NP6_shipped.rs"]mod shipped;
#[path="../../NP6_claims/src/NP6_reference.rs"]mod reference;
use core::{alloc::{GlobalAlloc,Layout},sync::atomic::{AtomicUsize,Ordering}};
static CALLS:AtomicUsize=AtomicUsize::new(0);
static SIZE:AtomicUsize=AtomicUsize::new(0);
static ALIGN:AtomicUsize=AtomicUsize::new(0);
struct Failing;
unsafe impl GlobalAlloc for Failing{
 unsafe fn alloc(&self,layout:Layout)->*mut u8{
  CALLS.fetch_add(1,Ordering::Relaxed);SIZE.store(layout.size(),Ordering::Relaxed);ALIGN.store(layout.align(),Ordering::Relaxed);
  core::ptr::null_mut()
 }
 unsafe fn dealloc(&self,_:*mut u8,_:Layout){panic!("failed allocation must not be deallocated");}
}
#[global_allocator]static ALLOCATOR:Failing=Failing;
#[cfg(kani)]#[kani::proof]#[kani::unwind(32)]
fn NP6_both_allocation_rejections(){
 let framed:[u8;3717]=kani::any();let root=[0u8;32];
 let prefix=r1_wire::np6_prefix(&root,&framed);
 CALLS.store(0,Ordering::Relaxed);
 let native=shipped::call(&prefix);
 assert!(matches!(native,Err(r1_wire::Error::Allocation)));
 assert!(CALLS.load(Ordering::Relaxed)==1);
 assert!(SIZE.load(Ordering::Relaxed)==1392);assert!(ALIGN.load(Ordering::Relaxed)==4);
 let owned=reference::call(&prefix);
 assert!(matches!(owned,Err(r1_wire::Error::Allocation)));
 assert!(CALLS.load(Ordering::Relaxed)==2);
 assert!(SIZE.load(Ordering::Relaxed)==1392);assert!(ALIGN.load(Ordering::Relaxed)==4);
}
