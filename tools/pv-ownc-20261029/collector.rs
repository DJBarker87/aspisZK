use aspis_statement::pool_v1::pair_tree_hiding::{PoolV1PairCopyRowLinkV1 as Link, PoolV1PairCopyRowLinkKindV1 as Kind};
use std::{alloc::{GlobalAlloc,Layout,System},sync::atomic::{AtomicUsize,Ordering},mem::{self,ManuallyDrop},ptr};
struct Alloc;
static WATCH:AtomicUsize=AtomicUsize::new(0);
static FREES:AtomicUsize=AtomicUsize::new(0);
unsafe impl GlobalAlloc for Alloc {
 unsafe fn alloc(&self,l:Layout)->*mut u8 {unsafe {System.alloc(l)}}
 unsafe fn dealloc(&self,p:*mut u8,l:Layout){if p as usize==WATCH.load(Ordering::SeqCst){FREES.fetch_add(1,Ordering::SeqCst);}unsafe{System.dealloc(p,l)}}
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8 {unsafe{System.realloc(p,l,n)}}
}
#[global_allocator] static ALLOC:Alloc=Alloc;
struct Prefix{inner:*mut Link,dst:*mut Link}
impl Drop for Prefix{fn drop(&mut self){unsafe{ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.inner,self.dst.offset_from_unsigned(self.inner)))}}}
struct Destination{ptr:*mut Link,len:usize,cap:usize}
impl Drop for Destination{fn drop(&mut self){unsafe{let _allocation=Vec::from_raw_parts(self.ptr,0,self.cap);ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.ptr,self.len));}}}
// Indexed-pointer owned reference. IntoIter supplies the same source read/tail
// guard as deployed std. POD permits forgetting the exhausted source instead
// of its four private header stores plus empty tail drop (Lean reset_no_free).
fn owned(v:Vec<Link>,mut keep:impl FnMut(&Link)->bool)->Vec<Link>{
 let p=v.as_ptr() as *mut Link;let cap=v.capacity();let mut source=v.into_iter();
 let sink=Prefix{inner:p,dst:p};
 let sink=source.try_fold(sink,|mut sink,item|->Result<Prefix, std::convert::Infallible>{
  if keep(&item){unsafe{ptr::write(sink.dst,item);sink.dst=sink.dst.add(1);}} Ok(sink)
 }).unwrap();
 let len=unsafe{ManuallyDrop::new(sink).dst.offset_from_unsigned(p)};
 let guard=Destination{ptr:p,len,cap};
 mem::forget(source); // Link POD; storage responsibility is now guard's.
 mem::forget(guard);unsafe{Vec::from_raw_parts(p,len,cap)}
}
fn values(v:&[Link])->Vec<(u16,u16)>{v.iter().map(|x|(x.producer_row,x.consumer_row)).collect()}
fn input(n:usize)->Vec<Link>{let mut v=Vec::with_capacity(n+7);for i in 0..n{v.push(Link{kind:Kind::SpongeCarry{from:i as u8,to:(!i) as u8},producer_row:i as u16,consumer_row:(i*31) as u16});}v}
fn run(n:usize,mode:usize,reference:bool,panic_at:Option<usize>){
 let v=input(n);let p=v.as_ptr() as usize;let cap=v.capacity();let expected=values(&v).into_iter().filter(|x|x.0 as usize%7<mode).collect::<Vec<_>>();
 WATCH.store(p,Ordering::SeqCst);FREES.store(0,Ordering::SeqCst);
 let mut count=0;let keep=|x:&Link|{if panic_at==Some(count){panic!("controlled predicate panic")};count+=1;x.producer_row as usize%7<mode};
 let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| if reference{owned(v,keep)}else{v.into_iter().filter(keep).collect::<Vec<_>>()}));
 match result{Ok(out)=>{assert_eq!(panic_at,None);assert_eq!(out.as_ptr() as usize,p);assert_eq!(out.capacity(),cap);assert_eq!(values(&out),expected);assert_eq!(FREES.load(Ordering::SeqCst),0);drop(out);},Err(_)=>{assert!(panic_at.is_some());}}
 assert_eq!(FREES.load(Ordering::SeqCst),1);WATCH.store(0,Ordering::SeqCst);
}
fn main(){
 assert_eq!((mem::size_of::<Link>(),mem::align_of::<Link>()),(8,2));assert!(!mem::needs_drop::<Link>());
 std::panic::set_hook(Box::new(|_|{}));let mut cases=0;
 for n in 0..=256{for mode in 0..=7{for reference in [false,true]{run(n,mode,reference,None);cases+=1;}}}
 for n in [1,2,7,16,64,127,128]{for k in 0..n{for reference in [false,true]{run(n,3,reference,Some(k));cases+=1;}}}
 println!("collector lifecycle cases={cases}; original/owned values, pointer, capacity, single free and predicate-unwind prefix; finite validation only");
}
