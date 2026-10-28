#![feature(try_reserve_kind)]
use std::{alloc::{GlobalAlloc,Layout,System},sync::atomic::{AtomicBool,AtomicUsize,Ordering},fmt::Debug,hint::black_box};
struct Audit;
static ACTIVE:AtomicBool=AtomicBool::new(false);
static FAIL:AtomicBool=AtomicBool::new(false);
static ALLOC:AtomicUsize=AtomicUsize::new(0);
static REALLOC:AtomicUsize=AtomicUsize::new(0);
static DEALLOC:AtomicUsize=AtomicUsize::new(0);
static DROPS:AtomicUsize=AtomicUsize::new(0);
unsafe impl GlobalAlloc for Audit{
 unsafe fn alloc(&self,l:Layout)->*mut u8{if ACTIVE.load(Ordering::SeqCst){ALLOC.fetch_add(1,Ordering::SeqCst);if FAIL.load(Ordering::SeqCst){return std::ptr::null_mut();}}System.alloc(l)}
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8{if ACTIVE.load(Ordering::SeqCst){REALLOC.fetch_add(1,Ordering::SeqCst);if FAIL.load(Ordering::SeqCst){return std::ptr::null_mut();}}System.realloc(p,l,n)}
 unsafe fn dealloc(&self,p:*mut u8,l:Layout){if ACTIVE.load(Ordering::SeqCst){DEALLOC.fetch_add(1,Ordering::SeqCst);}System.dealloc(p,l)}
}
#[global_allocator]static GLOBAL:Audit=Audit;
#[derive(Debug,PartialEq,Eq)]enum Error{Overflow,Allocation(usize,usize)}
#[inline(never)]fn native<T>(v:&mut Vec<T>,additional:usize)->Result<(),Error>{v.try_reserve_exact(additional).map_err(|e|match e.kind(){std::collections::TryReserveErrorKind::CapacityOverflow=>Error::Overflow,std::collections::TryReserveErrorKind::AllocError{layout,..}=>Error::Allocation(layout.size(),layout.align()),})}
#[inline(never)]fn reference<T>(v:&mut Vec<T>,additional:usize)->Result<(),Error>{
 let len=v.len();let cap=v.capacity();if additional<=cap-len{return Ok(());}
 if std::mem::size_of::<T>()==0{return Err(Error::Overflow);}
 let newcap=len.checked_add(additional).ok_or(Error::Overflow)?;
 let layout=Layout::array::<T>(newcap).map_err(|_|Error::Overflow)?;
 let p=unsafe{if cap==0{std::alloc::alloc(layout)}else{std::alloc::realloc(v.as_mut_ptr().cast(),Layout::array::<T>(cap).unwrap(),layout.size())}};
 if p.is_null(){return Err(Error::Allocation(layout.size(),layout.align()));}
 unsafe{std::ptr::write(v,Vec::from_raw_parts(p.cast::<T>(),len,newcap));}Ok(())
}
#[derive(Clone,Debug,PartialEq)]struct Tracked(u32);
impl Drop for Tracked{fn drop(&mut self){if ACTIVE.load(Ordering::SeqCst){DROPS.fetch_add(1,Ordering::SeqCst);}}}
#[allow(dead_code)]#[derive(Clone,Debug,PartialEq)]enum Word{Base(Vec<u32>),Secure(Vec<[u32;4]>)}
fn run<T:Clone+PartialEq+Debug>(n:usize,spare:usize,add:usize,fail:bool,make:fn(usize)->T,f:fn(&mut Vec<T>,usize)->Result<(),Error>)->(Result<(),Error>,usize,(usize,usize,usize,usize)){
 let mut v=Vec::with_capacity(n+spare);for i in 0..n{v.push(make(i));}let before=v.clone();let len=v.len();let cap=v.capacity();let p=v.as_ptr();
 for a in [&ALLOC,&REALLOC,&DEALLOC,&DROPS]{a.store(0,Ordering::SeqCst);}
 FAIL.store(fail,Ordering::SeqCst);ACTIVE.store(true,Ordering::SeqCst);
 let result=f(black_box(&mut v),black_box(add));
 ACTIVE.store(false,Ordering::SeqCst);FAIL.store(false,Ordering::SeqCst);
 let counts=(ALLOC.load(Ordering::SeqCst),REALLOC.load(Ordering::SeqCst),DEALLOC.load(Ordering::SeqCst),DROPS.load(Ordering::SeqCst));
 assert_eq!(v,before);assert_eq!(v.len(),len);assert_eq!(counts.2,0);assert_eq!(counts.3,0);
 if add<=cap-len{assert!(result.is_ok());assert_eq!(v.capacity(),cap);assert_eq!(v.as_ptr(),p);assert_eq!((counts.0,counts.1),(0,0));}
 else if result.is_ok(){assert_eq!(v.capacity(),len+add);assert_eq!((counts.0,counts.1),if cap==0{(1,0)}else{(0,1)});}
 else{assert_eq!(v.capacity(),cap);assert_eq!(v.as_ptr(),p);match &result{Err(Error::Overflow)=>assert_eq!((counts.0,counts.1),(0,0)),Err(Error::Allocation(size,align))=>{assert!(fail);assert_eq!(*size,(len+add)*std::mem::size_of::<T>());assert_eq!(*align,std::mem::align_of::<T>());assert_eq!((counts.0,counts.1),if cap==0{(1,0)}else{(0,1)});},_=>unreachable!()}}
 (result,v.capacity(),counts)
}
fn tests<T:Clone+PartialEq+Debug>(make:fn(usize)->T)->usize{let mut count=0;for n in 0..18{for spare in [0,3]{for add in [0,1,5,64,usize::MAX]{for fail in [false,true]{assert_eq!(run(n,spare,add,fail,make,native),run(n,spare,add,fail,make,reference));count+=1;}}}}count}
fn main(){assert_eq!(std::mem::size_of::<[u8;32]>(),32);assert_eq!(std::mem::size_of::<Vec<u32>>(),24);assert_eq!(std::mem::size_of::<Word>(),32);
 let count=tests(|i|i as u32)+tests(|i|[i as u8;32])+tests(|i|vec![i as u32,7])+tests(|i|Word::Base(vec![i as u32]))+tests(|i|Tracked(i as u32))+tests(|_|());
 println!("PASS {count} paired finite reserve cases: no-growth, fresh allocation, reallocation, injected null, capacity/layout overflow and ZST; exact inner error kind/layout, cap/len/data and alloc/realloc/dealloc/Drop counts. Native validation only.");}
