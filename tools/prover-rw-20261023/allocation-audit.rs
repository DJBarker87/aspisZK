//! Test harness only. Compile with --cfg prover_rw_allocation_audit.
use std::alloc::{GlobalAlloc,Layout,System};
use std::sync::atomic::{AtomicUsize,Ordering::Relaxed};
pub struct CountingAllocator;
static ALLOCATIONS:AtomicUsize=AtomicUsize::new(0);
static REALLOCATIONS:AtomicUsize=AtomicUsize::new(0);
static REQUESTED:AtomicUsize=AtomicUsize::new(0);
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self,l:Layout)->*mut u8 {
        ALLOCATIONS.fetch_add(1,Relaxed);REQUESTED.fetch_add(l.size(),Relaxed);
        unsafe {System.alloc(l)}
    }
    unsafe fn alloc_zeroed(&self,l:Layout)->*mut u8 {
        ALLOCATIONS.fetch_add(1,Relaxed);REQUESTED.fetch_add(l.size(),Relaxed);
        unsafe {System.alloc_zeroed(l)}
    }
    unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8 {
        REALLOCATIONS.fetch_add(1,Relaxed);REQUESTED.fetch_add(n,Relaxed);
        unsafe {System.realloc(p,l,n)}
    }
    unsafe fn dealloc(&self,p:*mut u8,l:Layout) {unsafe {System.dealloc(p,l)}}
}
pub fn reset() {ALLOCATIONS.store(0,Relaxed);REALLOCATIONS.store(0,Relaxed);REQUESTED.store(0,Relaxed);}
pub fn counts()->[usize;3] {[ALLOCATIONS.load(Relaxed),REALLOCATIONS.load(Relaxed),REQUESTED.load(Relaxed)]}
