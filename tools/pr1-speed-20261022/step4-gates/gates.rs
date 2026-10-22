extern crate alloc;
#[path="../../../docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs"]
mod workers;
#[path="lift_gate.rs"]
mod gate;
fn main() {}
#[cfg(test)] mod tests {
 use super::*;
 use std::sync::atomic::{AtomicUsize,Ordering};
 #[test] fn rank_gate_accept_reject_and_panic() {
  for trial in 0..64 {
   for result in [Some(false),Some(true),None] {
    let gate=gate::LiftGate::default();
    let expensive=AtomicUsize::new(0);
    let got=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||workers::ordered_families(3,|i| {
     if i==1 {
      let _guard=gate::LiftGateGuard(&gate);
      for _ in 0..trial%5 {std::thread::yield_now();}
      match result {Some(ok)=>{gate.publish(ok);ok},None=>panic!("first lift")}
     } else {
      let ok=gate.wait();
      if ok {expensive.fetch_add(1,Ordering::SeqCst);}
      ok
     }
    })));
    if let Some(ok)=result {assert_eq!(got.unwrap(),vec![ok;3]);}else{assert!(got.is_err());}
    assert_eq!(expensive.load(Ordering::SeqCst),if result==Some(true){2}else{0});
   }
  }
 }
}
