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
static DROPS:AtomicUsize=AtomicUsize::new(0);
struct Z;
impl Drop for Z {fn drop(&mut self){DROPS.fetch_add(1,Ordering::SeqCst);}}
fn main(){
 for n in 0usize..=32 {
  let mut a:Vec<Z>=(0..n).map(|_|Z).collect();
  let mut b:Vec<Z>=(0..n).map(|_|Z).collect();
  let ap=a.as_ptr();let bp=b.as_ptr();
  let ac=a.capacity();let bc=b.capacity();
  let d=DROPS.load(Ordering::SeqCst);
  reset();let x=a.pop();let aw=counts();let ad=DROPS.load(Ordering::SeqCst);
  reset();let y=pop_move_reference(&mut b);let bw=counts();let bd=DROPS.load(Ordering::SeqCst);
  assert_eq!(aw,(0,0,0));assert_eq!(bw,aw);assert_eq!(ad,d);assert_eq!(bd,d);
  assert_eq!(a.as_ptr(),ap);assert_eq!(b.as_ptr(),bp);
  assert_eq!(a.capacity(),ac);assert_eq!(b.capacity(),bc);assert_eq!(ac,usize::MAX);
  assert_eq!(x.is_some(),n>0);assert_eq!(y.is_some(),n>0);
  assert_eq!(a.len(),n.saturating_sub(1));assert_eq!(b.len(),a.len());
 }
 println!("PASS 33 non-Copy Drop ZST cases; zero allocator and Drop calls during both operations; pointer/capacity retained");
}
