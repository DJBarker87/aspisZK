use super::{QM31,q};
#[derive(Clone,Copy)] struct Event {left:QM31,right:QM31,reply:QM31}
struct Log {used:usize,events:[Event;2],frame:[u32;8]}
// Each call gets an independent full reply, even when its arguments repeat.
// Modifies: only this harness-local log's next slot and used count.
fn mul(left:QM31,right:QM31,log:&mut Log)->QM31 {
 assert!(log.used<2);let reply=q();log.events[log.used]=Event{left,right,reply};log.used+=1;reply
}
pub fn caller() {
 let a=q();let b=q();let frame=kani::any();
 let mut log=Log{used:0,events:[Event{left:QM31::ZERO,right:QM31::ZERO,reply:QM31::ZERO};2],frame};
 // Erasure of mul(...,&mut log) to a.mul(b) gives the frozen pair of calls.
 let first=mul(a,b,&mut log);let second=mul(a,b,&mut log);
 if cfg!(feature="negative-control") {
  let mode=crate::mutation();let limb=mode%4;
  let target=if mode<4 {&mut log.events[1].reply}else if mode<8 {&mut log.events[0].left}else {&mut log.events[0].right};
  match limb {0=>target.c0.a.0^=1,1=>target.c0.b.0^=1,2=>target.c1.a.0^=1,_=>target.c1.b.0^=1};
 }
 // Explicit G(args,log) returns both replies. Equality between the replies is
 // deliberately absent: only the actual deterministic child's bridge can add it.
 assert_eq!((first,second),(log.events[0].reply,log.events[1].reply));
 assert_eq!(log.used,2);assert_eq!(log.frame,frame);
 let mut i=0;while i<2 {assert_eq!(log.events[i].left,a);assert_eq!(log.events[i].right,b);i+=1;}
}
