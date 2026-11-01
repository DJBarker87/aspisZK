use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize,Ordering};
struct Tracked;
static ALLOCS: AtomicUsize=AtomicUsize::new(0);
static REALLOCS: AtomicUsize=AtomicUsize::new(0);
static DEALLOCS: AtomicUsize=AtomicUsize::new(0);
unsafe impl GlobalAlloc for Tracked {
 unsafe fn alloc(&self,l:Layout)->*mut u8 { ALLOCS.fetch_add(1,Ordering::SeqCst);System.alloc(l) }
 unsafe fn dealloc(&self,p:*mut u8,l:Layout){ DEALLOCS.fetch_add(1,Ordering::SeqCst);System.dealloc(p,l) }
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8 { REALLOCS.fetch_add(1,Ordering::SeqCst);System.realloc(p,l,n) }
}
#[global_allocator] static A:Tracked=Tracked;
fn reset(){ALLOCS.store(0,Ordering::SeqCst);REALLOCS.store(0,Ordering::SeqCst);DEALLOCS.store(0,Ordering::SeqCst);}
fn counts()->(usize,usize,usize){(ALLOCS.load(Ordering::SeqCst),REALLOCS.load(Ordering::SeqCst),DEALLOCS.load(Ordering::SeqCst))}
include!("move-reference.rs");
fn main() {
 let mut checks=0;
 for n in 0..=32 {
  for spare in [0,1,17] {
   let mut native:Vec<Result<Vec<u32>,Vec<u8>>>=Vec::with_capacity(n+spare);
   let mut reference:Vec<Result<Vec<u32>,Vec<u8>>>=Vec::with_capacity(n+spare);
   for i in 0..n {
    let item=if i%2==0 {Ok(vec![i as u32,29])} else {Err(vec![17,i as u8])};
    native.push(item.clone());reference.push(item);
   }
   let np=native.as_ptr();let nc=native.capacity();
   let rp=reference.as_ptr();let rc=reference.capacity();
   reset();let a=native.pop();let aw=counts();
   reset();let b=pop_move_reference(&mut reference);let bw=counts();
   assert_eq!(aw,(0,0,0));assert_eq!(bw,aw);
   assert_eq!(native.as_ptr(),np);assert_eq!(native.capacity(),nc);
   assert_eq!(reference.as_ptr(),rp);assert_eq!(reference.capacity(),rc);
   assert_eq!(a,b);assert_eq!(native,reference);
   checks+=1;
  }
 }
 println!("{{\"status\":\"PASS\",\"checks\":{},\"payload\":\"Result<Vec<u32>,Vec<u8>> (non-Copy)\",\"native_allocations\":0,\"reference_allocations\":0,\"native_reallocations\":0,\"reference_reallocations\":0,\"native_deallocations\":0,\"reference_deallocations\":0,\"buffers_and_capacities_retained\":true}}",checks);
}
