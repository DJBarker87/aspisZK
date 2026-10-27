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
pub fn pop_slices_reference<T:Copy>(v:&[T],out:&mut Vec<T>)->Option<T> {
    if v.len()==0 {None} else {
        let last=v.len()-1;let mut i=0;
        while i<last {out.push(v[i]);i+=1;}
        Some(v[last])
    }
}

fn main() {
 let mut native=Vec::with_capacity(2);native.push(17u8);native.push(29u8);
 let raw=[17u8,29u8];let mut tail=Vec::new();
 let ptr=native.as_ptr();let cap=native.capacity();
 reset();let n=native.pop();let nw=counts();
 let retains_buffer=native.as_ptr()==ptr && native.capacity()==cap;
 reset();let r=pop_slices_reference(&raw,&mut tail);let rw=counts();
 let equal_value=n==r && native==tail;
 assert!(equal_value);assert!(retains_buffer);assert_eq!(nw,(0,0,0));
 assert!(rw.0>0);assert_ne!(nw,rw);
 println!("{{\"status\":\"CHECKED_COUNTEREXAMPLE\",\"input\":[17,29],\"native_result\":{{\"returned\":29,\"tail\":[17]}},\"reference_result\":{{\"returned\":29,\"tail\":[17]}},\"value_equal\":{},\"native_retains_buffer\":{},\"native_world\":{{\"alloc\":{},\"realloc\":{},\"dealloc\":{}}},\"reference_world\":{{\"alloc\":{},\"realloc\":{},\"dealloc\":{}}}}}",equal_value,retains_buffer,nw.0,nw.1,nw.2,rw.0,rw.1,rw.2);
}
