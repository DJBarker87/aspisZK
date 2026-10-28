use std::alloc::{GlobalAlloc,Layout,System};
use std::sync::atomic::{AtomicBool,AtomicUsize,Ordering::SeqCst};
use aspis_statement::pool_v1::{pair_forest_hiding as forest,pair_tree_hiding::PoolV1PairCopyRowLinkV1 as Link};
mod owned133;
mod reference133;
struct A;
static ON:AtomicBool=AtomicBool::new(false);
static COUNT:AtomicUsize=AtomicUsize::new(0);
static FAIL:AtomicUsize=AtomicUsize::new(0);
extern "C" {fn write(fd:i32,p:*const u8,n:usize)->isize;}
fn num(b:&mut [u8;128],i:&mut usize,mut n:usize){let mut a=[0u8;24];let mut k=0;loop {a[k]=b'0'+(n%10)as u8;k+=1;n/=10;if n==0 {break}}for j in (0..k).rev(){b[*i]=a[j];*i+=1;}}
fn event(kind:u8,size:usize,align:usize,new:usize)->bool{
 if !ON.load(SeqCst){return false}
 let n=COUNT.fetch_add(1,SeqCst)+1;let fail=FAIL.load(SeqCst)==n;
 let mut b=[0u8;128];let mut i=0;b[i]=kind;i+=1;
 for v in [n,size,align,new,fail as usize]{b[i]=b' ';i+=1;num(&mut b,&mut i,v)}b[i]=b'\n';i+=1;
 unsafe{write(2,b.as_ptr(),i);}
 fail
}
unsafe impl GlobalAlloc for A {
 unsafe fn alloc(&self,l:Layout)->*mut u8 {if event(b'A',l.size(),l.align(),0){std::ptr::null_mut()}else{System.alloc(l)}}
 unsafe fn alloc_zeroed(&self,l:Layout)->*mut u8 {if event(b'Z',l.size(),l.align(),0){std::ptr::null_mut()}else{System.alloc_zeroed(l)}}
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8 {if event(b'R',l.size(),l.align(),n){std::ptr::null_mut()}else{System.realloc(p,l,n)}}
 unsafe fn dealloc(&self,p:*mut u8,l:Layout){event(b'D',l.size(),l.align(),0);System.dealloc(p,l)}
}
#[global_allocator]static ALLOC:A=A;
fn main(){
 let args:Vec<_>=std::env::args().collect();let fail=args.get(1).map(|s|s.parse::<usize>().unwrap()).unwrap_or(0);
 let mask=args.get(2).map(|s|s=="mask").unwrap_or(false);
 let owned=args.get(2).map(|s|s=="owned").unwrap_or(false);
 FAIL.store(fail,SeqCst);COUNT.store(0,SeqCst);ON.store(true,SeqCst);
 if mask {let m=forest::pool_v1_pair_forest_copy_active_row_masks_v1().unwrap();ON.store(false,SeqCst);println!("masks {:?}",m)}
 else {let rows=if owned {owned133::forest::pool_v1_pair_forest_copy_active_rows_v1().unwrap()}else{forest::pool_v1_pair_forest_copy_active_rows_v1().unwrap()};assert_eq!(rows.as_slice(),&reference133::active_rows());let len=rows.len();let cap=rows.capacity();let sum:usize=rows.iter().map(|x|*x as usize).sum();drop(rows);ON.store(false,SeqCst);println!("rows len={len} cap={cap} sum={sum}");}
 println!("link size={} align={}",std::mem::size_of::<Link>(),std::mem::align_of::<Link>());
}
