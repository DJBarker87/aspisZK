use super::{q,QM31};
#[derive(Clone,Copy)] pub struct Selectors {pub high:[QM31;64],pub low:[QM31;16]}
#[derive(Clone,Copy)] struct Event {left:QM31,right:QM31,reply:QM31}
pub struct Log {used:usize,events:[Event;64],frame:[u32;8]}
impl Log {pub fn new(frame:[u32;8])->Self {Self{used:0,events:[Event{left:QM31::ZERO,right:QM31::ZERO,reply:QM31::ZERO};64],frame}}}
// Full QM31 reply: every raw limb unconstrained. Modifies only used and the
// appended log slot. The child has no mutable arguments or external effects.
fn add(left:QM31,right:QM31,log:&mut Log)->QM31 {
 assert!(log.used<64);let reply=q();log.events[log.used]=Event{left,right,reply};log.used+=1;reply
}
// Erasing the added log argument and add interception gives the exact frozen
// sum_high caller. Input borrow place and all loop/lookup order are retained.
pub fn sum_high(selectors:&Selectors,ranges:&[core::ops::Range<usize>],log:&mut Log)->QM31 {
 let mut sum=QM31::ZERO;
 for range in ranges {
  for block in range.clone() {
   sum=add(sum,selectors.high[block],log);
  }
 }
 sum
}
// G checks the complete ordered arguments and pre-state chain, then returns
// the final full reply. No equality with actual field addition is assumed.
pub fn model(high:&[QM31;64],ranges:&[core::ops::Range<usize>],log:&Log)->QM31 {
 let mut previous=QM31::ZERO;let mut count=0;let mut i=0;
 while i<ranges.len() {
  let mut block=ranges[i].start;
  while block<ranges[i].end {
   assert!(block<64);assert!(count<log.used);
   let e=log.events[count];assert_eq!(e.left,previous);assert_eq!(e.right,high[block]);
   previous=e.reply;count+=1;block+=1;
  }
  i+=1;
 }
 assert_eq!(count,log.used);previous
}
pub fn check(high:[QM31;64],low:[QM31;16],ranges:&[core::ops::Range<usize>]) {
 let frame=kani::any();let mut log=Log::new(frame);let mut selectors=Selectors{high,low};
 let actual=sum_high(&selectors,ranges,&mut log);
 if cfg!(feature="negative-control") {
  match crate::mutation() {
   0=>log.events[log.used-1].reply.c0.a.0^=1,
   1=>log.events[0].left.c0.a.0^=1,
   2=>log.events[0].right.c0.a.0^=1,
   3=>log.frame[0]^=1,
   4=>log.used-=1,
   _=>selectors.high[ranges[0].start].c0.a.0^=1,
  }
 }
 assert_eq!(actual,model(&high,ranges,&log));
 assert_eq!(log.frame,frame);assert_eq!(selectors.high,high);assert_eq!(selectors.low,low);
}
