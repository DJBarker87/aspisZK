use std::{alloc::{GlobalAlloc,Layout,System},mem::ManuallyDrop,sync::atomic::{AtomicBool,AtomicUsize,Ordering},hint::black_box};
struct Audit;
static ACTIVE:AtomicBool=AtomicBool::new(false);
static ALLOC:AtomicUsize=AtomicUsize::new(0);
static REALLOC:AtomicUsize=AtomicUsize::new(0);
static FREE:AtomicUsize=AtomicUsize::new(0);
static BYTES:AtomicUsize=AtomicUsize::new(0);
static ADDRESS:AtomicUsize=AtomicUsize::new(0);
unsafe impl GlobalAlloc for Audit {
 unsafe fn alloc(&self,l:Layout)->*mut u8 {if ACTIVE.load(Ordering::SeqCst){ALLOC.fetch_add(1,Ordering::SeqCst);} System.alloc(l)}
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8{if ACTIVE.load(Ordering::SeqCst){REALLOC.fetch_add(1,Ordering::SeqCst);}System.realloc(p,l,n)}
 unsafe fn dealloc(&self,p:*mut u8,l:Layout){if ACTIVE.load(Ordering::SeqCst){FREE.fetch_add(1,Ordering::SeqCst);BYTES.store(l.size(),Ordering::SeqCst);ADDRESS.store(p as usize,Ordering::SeqCst);assert_eq!(l.align(),4);}System.dealloc(p,l)}
}
#[global_allocator] static GLOBAL:Audit=Audit;
#[inline(never)] fn native(v:Vec<u32>){core::mem::drop(black_box(v));}
#[inline(never)] fn reference(v:Vec<u32>){let mut v=ManuallyDrop::new(black_box(v));let p=v.as_mut_ptr();let len=v.len();let cap=v.capacity();unsafe{std::ptr::drop_in_place(std::ptr::slice_from_raw_parts_mut(p,len));if cap!=0 {std::alloc::dealloc(p.cast(),Layout::array::<u32>(cap).unwrap());}}}
fn run(n:usize,spare:usize, f:fn(Vec<u32>))->(usize,usize,usize,usize){
 let mut v=Vec::with_capacity(n+spare);v.extend((0..n).map(|i|(i as u32).wrapping_mul(0xdeadbeef)));let cap=v.capacity();let p=v.as_ptr() as usize;
 for a in [&ALLOC,&REALLOC,&FREE,&BYTES,&ADDRESS] {a.store(0,Ordering::SeqCst);}
 ACTIVE.store(true,Ordering::SeqCst);f(v);ACTIVE.store(false,Ordering::SeqCst);
 let observed=(ALLOC.load(Ordering::SeqCst),REALLOC.load(Ordering::SeqCst),FREE.load(Ordering::SeqCst),BYTES.load(Ordering::SeqCst));
 assert_eq!(observed,(0,0,usize::from(cap!=0),4*cap));if cap!=0{assert_eq!(ADDRESS.load(Ordering::SeqCst),p);}
 observed
}
fn main(){assert!(!std::mem::needs_drop::<u32>());assert!(std::mem::needs_drop::<Vec<u32>>());let mut count=0;for n in 0..65{for spare in [0,1,7,32]{assert_eq!(run(n,spare,native),run(n,spare,reference));count+=1;}}println!("PASS {count} paired finite cases Vec<u32>: 0 alloc/realloc, free iff capacity>0, exact pointer/layout, no u32 destructors; no claim about binary erasure or unbounded allocator refinement");}
