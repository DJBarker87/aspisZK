extern crate alloc;
#[path="../../../docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs"]
mod production;
#[cfg(kani)]
mod proofs {
 use super::production::*;
 #[kani::proof]
 fn ordered_partition() {
  let n:usize=kani::any();let k:usize=kani::any();kani::assume(k<THREADS);
  let (a,b)=range(n,k);
  assert!(a<=b && b<=n);
  assert!(b-a<=n/THREADS+1);
  if k==0 {assert_eq!(a,0);}
  if k+1<THREADS {assert_eq!(b,range(n,k+1).0);}else{assert_eq!(b,n);}
 }
}
#[cfg(test)]
mod tests {
 use super::production::*;
 #[test]
 fn schedules_nested_teams_and_panic_order() {
  use std::sync::atomic::{AtomicUsize,Ordering::*};
  let live=AtomicUsize::new(0);let peak=AtomicUsize::new(0);
  for trial in 0..32 {
   let ids=std::sync::Mutex::new(std::collections::HashSet::new());
   let result=ordered_map(64+trial,|i|{
    let count=live.fetch_add(1,SeqCst)+1;peak.fetch_max(count,SeqCst);
    for _ in 0..((i*13+trial)%7){std::thread::yield_now();}
    ids.lock().unwrap().insert(std::thread::current().id());
    let nested=ordered_map(32,|j|{ids.lock().unwrap().insert(std::thread::current().id());i*32+j});
    live.fetch_sub(1,SeqCst);nested
   });
   assert_eq!(result,(0..64+trial).map(|i|(0..32).map(|j|i*32+j).collect::<Vec<_>>()).collect::<Vec<_>>());
   assert!(ids.lock().unwrap().len()<=THREADS);
   assert_eq!(live.load(SeqCst),0);assert!(peak.load(SeqCst)<=THREADS);assert!(!is_worker());
  }
  for fail in [0,3,17,33,63] {
   let result=std::panic::catch_unwind(||ordered_map(64,|i|{if i==fail || i==63 {std::panic::panic_any(i);}i}));
   let panic=result.unwrap_err();assert_eq!(*panic.downcast::<usize>().unwrap(),fail);assert!(!is_worker());
  }
  assert_eq!(ordered_families(3,|i|i),vec![0,1,2]);
 }
}
#[cfg(test)]
#[path="../stage2-gates/reference_check.rs"]
mod reference;
#[cfg(test)]
mod checker_tests {
 use super::reference;
 fn outcome(f:impl FnOnce()->bool)->Option<bool>{std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).ok()}
 #[test]
 fn worker_products_and_entries_match_reference() {
  let mut seed=0x123498abcd_u64;
  let mut word=||{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;seed as u32};
  for trial in 0..128 {
   let ni=32+(word()%18)as usize;let nj=(word()%9)as usize;let len=(word()%9)as usize;
   let a:Vec<u32>=(0..ni*len).map(|_|word()).collect();
   let b:Vec<u32>=(0..len*nj).map(|_|word()).collect();
   let mut c:Vec<u32>=(0..ni).flat_map(|i|(0..nj).map(move|j|(i,j))).map(|(i,j)|reference::dot(&a,i*len,1,&b,j,nj,len)as u32).collect();
   if trial%2==1 && !c.is_empty(){c[0]^=1;}
   if trial%4==3 && !c.is_empty(){c.pop();}
   assert_eq!(outcome(||reference::prod_ok(&a,0,&b,0,&c,0,ni,nj,len)),outcome(||aspis_r1_cert_check::prod_ok(&a,0,&b,0,&c,0,ni,nj,len)));
   let mut ej=vec![0u32;ni];let es=vec![0u32;ni];let epo=vec![0u32;ni];let eco=vec![0u32;ni];
   let mut out=vec![0u32;ni];if trial%2==1 {out[ni-1]=1;}if trial%4==3 {ej[0]=999;}
   let check=|native:bool|{
    if native {aspis_r1_cert_check::ents_ok(&ej,&es,&epo,&eco,&[],&[],ni,&[0],&[1],&[0],1,&[],1,0,&[0],1,1,&out,&[0])}
    else {reference::ents_ok(&ej,&es,&epo,&eco,&[],&[],ni,&[0],&[1],&[0],1,&[],1,0,&[0],1,1,&out,&[0])}
   };
   assert_eq!(outcome(||check(false)),outcome(||check(true)));
  }
 }
}
