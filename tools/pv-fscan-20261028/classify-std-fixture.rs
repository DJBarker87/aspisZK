use std::alloc::{GlobalAlloc,Layout,System};
use std::sync::atomic::{AtomicBool,AtomicUsize,Ordering};
struct Audit;static ACTIVE:AtomicBool=AtomicBool::new(false);static CALLS:AtomicUsize=AtomicUsize::new(0);
unsafe impl GlobalAlloc for Audit {
 unsafe fn alloc(&self,l:Layout)->*mut u8 {if ACTIVE.load(Ordering::SeqCst){CALLS.fetch_add(1,Ordering::SeqCst);}System.alloc(l)}
 unsafe fn dealloc(&self,p:*mut u8,l:Layout){System.dealloc(p,l)}
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8{if ACTIVE.load(Ordering::SeqCst){CALLS.fetch_add(1,Ordering::SeqCst);}System.realloc(p,l,n)}
}
#[global_allocator]static A:Audit=Audit;
fn main(){
 for n in 0..=1024 {
  let s=String::with_capacity(n);let reference=Vec::<u8>::with_capacity(n);
  assert_eq!(s.as_bytes(),reference);assert_eq!(s.len(),0);assert!(s.capacity()>=n);assert!(reference.capacity()>=n);
 }
 ACTIVE.store(true,Ordering::SeqCst);let a=Vec::<u32>::default();let b=Vec::<u32>::new();ACTIVE.store(false,Ordering::SeqCst);
 assert_eq!(CALLS.load(Ordering::SeqCst),0);assert_eq!(a,b);assert_eq!(a.len(),0);assert_eq!(a.capacity(),0);assert_eq!(b.capacity(),0);
 println!("FINITE: V181 1025 String/Vec capacity pairs; V186 default/new Vec<u32> empty headers with no allocation; no allocator-failure or universal world claim");
}
