use std::alloc::{GlobalAlloc,Layout,System};
use std::sync::atomic::{AtomicBool,AtomicUsize,Ordering::SeqCst};
use std::path::PathBuf;
struct Trace;
static ACTIVE:AtomicBool=AtomicBool::new(false);
static COUNT:AtomicUsize=AtomicUsize::new(0);
static EVENTS:[AtomicUsize;256]=[const{AtomicUsize::new(0)};256];
fn event(kind:usize,old:usize,new:usize){
 if ACTIVE.load(SeqCst){let i=COUNT.fetch_add(1,SeqCst)*3;assert!(i+2<256);EVENTS[i].store(kind,SeqCst);EVENTS[i+1].store(old,SeqCst);EVENTS[i+2].store(new,SeqCst);}
}
unsafe impl GlobalAlloc for Trace{
 unsafe fn alloc(&self,l:Layout)->*mut u8{event(1,0,l.size());System.alloc(l)}
 unsafe fn dealloc(&self,p:*mut u8,l:Layout){event(3,l.size(),0);System.dealloc(p,l)}
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8{event(2,l.size(),n);System.realloc(p,l,n)}
}
#[global_allocator] static ALLOC:Trace=Trace;
fn start(){COUNT.store(0,SeqCst);ACTIVE.store(true,SeqCst);}
fn stop()->Vec<(usize,usize,usize)>{ACTIVE.store(false,SeqCst);(0..COUNT.load(SeqCst)).map(|i|(EVENTS[3*i].load(SeqCst),EVENTS[3*i+1].load(SeqCst),EVENTS[3*i+2].load(SeqCst))).collect()}
#[inline(never)] fn owned(base:&std::path::Path,name:String)->PathBuf{base.join(name)}
#[inline(never)] fn borrowed(base:&std::path::Path,name:&String)->PathBuf{base.join(name)}
fn main(){
 let base=PathBuf::from("base");
 let mut name=String::with_capacity(69);for _ in 0..64{name.push('a');}name.push_str(".burn");
 assert_eq!(name.len(),69);assert_eq!(name.capacity(),69);
 let mut copy=String::with_capacity(69);copy.push_str(&name);
 start();let a=std::hint::black_box(owned(&base,name));let owned_events=stop();
 start();let b=std::hint::black_box(borrowed(&base,&copy));let borrowed_events=stop();
 assert_eq!(a,b);assert_eq!(owned_events,vec![(1,0,4),(2,4,8),(2,8,74),(3,69,0)]);
 assert_eq!(borrowed_events,vec![(1,0,4),(2,4,8),(2,8,74)]);
 println!("owned={owned_events:?}\nborrowed={borrowed_events:?}\nvalue_bytes={}",a.as_os_str().len());
}
