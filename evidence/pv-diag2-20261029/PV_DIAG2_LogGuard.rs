//! Finite controls for the exact deployed log facade, not a native caller-closure proof.
use std::sync::atomic::{AtomicUsize,Ordering};
use log::{Level,LevelFilter,Log,Metadata,Record};
struct Observer<'a>(&'a AtomicUsize);
impl Log for Observer<'_>{fn enabled(&self,_:&Metadata)->bool{true} fn log(&self,_:&Record){self.0.fetch_add(1,Ordering::SeqCst);} fn flush(&self){}}
fn main(){
 assert_eq!(log::STATIC_MAX_LEVEL,LevelFilter::Trace);
 assert_eq!(log::max_level(),LevelFilter::Off);
 let args=AtomicUsize::new(0usize);let received=AtomicUsize::new(0usize);let logger=Observer(&received);let mut cases=0;
 for enabled in [false,true]{
  log::set_max_level(if enabled{LevelFilter::Trace}else{LevelFilter::Off});
  for level in [Level::Error,Level::Warn,Level::Info,Level::Debug,Level::Trace]{
   let a=args.load(Ordering::SeqCst);let r=received.load(Ordering::SeqCst);
   log::log!(logger:&logger,level,"{}",{args.fetch_add(1,Ordering::SeqCst);17});
   assert_eq!(args.load(Ordering::SeqCst)-a,if enabled{1}else{0});assert_eq!(received.load(Ordering::SeqCst)-r,if enabled{1}else{0});cases+=1;
  }
 }
 println!("{{\"cases\":{cases},\"arguments_evaluated\":{},\"dispatched\":{}}}",args.load(Ordering::SeqCst),received.load(Ordering::SeqCst));
}
