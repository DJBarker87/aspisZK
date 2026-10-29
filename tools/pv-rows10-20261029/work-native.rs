extern crate alloc;
#[path="/home/dombarker/project-offloads/codex-pv-fscan-20261028/src/crates/aspis-r1-cost-probe/src/host_work.rs"]
mod work;
#[path="/home/dombarker/project-offloads/codex-pv-fscan-20261028/src/docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs"]
mod ranges;
use std::sync::atomic::{AtomicUsize,Ordering};
fn main(){
 let mut range_cases=0usize;
 for n in (0..4097).chain([usize::MAX,usize::MAX-1,usize::MAX-15,usize::MAX/2]) {
  let mut end=0;
  for k in 0..16 {let (a,b)=ranges::range(n,k);assert_eq!(a,end);assert!(a<=b && b<=n);end=b;range_cases+=1;}
  assert_eq!(end,n);
 }
 let mut map_cases=0;
 for n in [0,1,15,16,17,31,32,33,127,1024] {
  let calls:Vec<_>=(0..n).map(|_|AtomicUsize::new(0)).collect();
  let v=work::map(3,n,|i|{calls[i].fetch_add(1,Ordering::SeqCst);i});
  assert_eq!(v,(0..n).collect::<Vec<_>>());for c in calls{assert_eq!(c.load(Ordering::SeqCst),1);}map_cases+=1;
 }
 let nested=work::map(4,32,|i|work::map(5,2,|j|i*2+j));
 assert_eq!(nested,(0..32).map(|i|vec![i*2,i*2+1]).collect::<Vec<_>>());
 let result=std::panic::catch_unwind(||work::map(6,32,|i|{if i==0{panic!("first-source-panic")};if i==17{panic!("later-source-panic")};i}));
 let e=result.unwrap_err();assert_eq!(e.downcast_ref::<&str>().copied(),Some("first-source-panic"));
 println!("{{\"range_cases\":{range_cases},\"map_cases\":{map_cases},\"nested_ordered\":true,\"source_order_panic\":true,\"classification\":\"finite validation; no universal runtime association\"}}");
}
