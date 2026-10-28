use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst};
use std::{path::Path, ffi::OsStr, os::unix::ffi::OsStrExt};
struct Trace;
static ACTIVE: AtomicBool=AtomicBool::new(false);
static COUNT: AtomicUsize=AtomicUsize::new(0);
static EVENTS: [AtomicUsize;64]=[const {AtomicUsize::new(0)};64];
fn event(kind:usize,n:usize) {if ACTIVE.load(SeqCst) {let i=COUNT.fetch_add(1,SeqCst);assert!(i<64);EVENTS[i].store(n*4+kind,SeqCst);}}
unsafe impl GlobalAlloc for Trace {
 unsafe fn alloc(&self,l:Layout)->*mut u8 {event(0,l.size());System.alloc(l)}
 unsafe fn dealloc(&self,p:*mut u8,l:Layout) {event(1,l.size());System.dealloc(p,l)}
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8 {event(2,n);System.realloc(p,l,n)}
}
#[global_allocator] static ALLOC:Trace=Trace;
fn trace<T>(f:impl FnOnce()->T)->(T,Vec<usize>) {
 COUNT.store(0,SeqCst);ACTIVE.store(true,SeqCst);let v=f();ACTIVE.store(false,SeqCst);
 let e=(0..COUNT.load(SeqCst)).map(|i|EVENTS[i].load(SeqCst)).collect();(v,e)
}
fn old(base:&[u8],path:&[u8])->Vec<u8> {
 let mut out=Vec::new();
 if path.len()>0 && path[0]==b'/' {out.extend_from_slice(path);}
 else {out.extend_from_slice(base);if base.len()>0 && base[base.len()-1]!=b'/' {out.push(b'/');}out.extend_from_slice(path);}
 out
}
fn repaired(base:&[u8],path:&[u8])->Vec<u8> {
 let mut out=base.to_vec();
 if path.first()==Some(&b'/') {out.truncate(0);}
 else if !base.is_empty() && base.last()!=Some(&b'/') {out.extend_from_slice(b"/");}
 out.extend_from_slice(path);out
}
fn main() {
 std::panic::set_hook(Box::new(|_|{}));
 let n=isize::MAX as usize+1;
 assert!(std::panic::catch_unwind(||String::with_capacity(n)).is_err());
 assert!(std::panic::catch_unwind(||String::new()).is_ok());
 println!("V181 checked counterexample n={n}: deployed panic; old empty reference returns. No allocator failure needed.");
 let (a,ae)=trace(||Path::new("base").join("/"));
 let (b,be)=trace(||old(b"base",b"/"));
 assert_eq!(a.as_os_str().as_bytes(),b);assert_ne!(ae,be);
 println!("V178 checked effect counterexample base=base path=/: native events={ae:?}; old reference events={be:?}; encoding=4*size+kind (alloc0,dealloc1,realloc2). Contents equal.");
 let mut cases=0;
 let corpus=[b"".as_slice(),b"base",b"/",b"//",b"a/",b"a//b",b"\x80\xff",b"\0"];
 for base in corpus {for path in corpus {
  let (a,ae)=trace(||Path::new(OsStr::from_bytes(base)).join(OsStr::from_bytes(path)));
  let (b,be)=trace(||repaired(base,path));
  assert_eq!(a.as_os_str().as_bytes(),b);assert_eq!(ae,be,"{base:?} {path:?}");cases+=1;
 }}
 println!("PASS repaired V178 {cases} value/allocation-event pairs; finite validation only");
}
