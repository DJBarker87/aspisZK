//! Exact native CoinOracle body against an explicit-state reference.
//! Table is the D133 ordered-map contract projected to this call's key.
//! This proves RefCell/control/effects, not Rust B-tree internals.
use std::cell::RefCell;
trait Digest32 { fn digest(&self,parts:&[&[u8]])->[u8;32]; }
#[derive(Clone,Debug,PartialEq)]
struct Table { previous:Option<[u8;32]>, written:Option<(Vec<u8>,[u8;32])> }
impl Table {
 fn insert(&mut self, key:Vec<u8>, answer:[u8;32])->Option<[u8;32]> {
  let old=self.previous;self.previous=Some(answer);self.written=Some((key,answer));old
 }
}
fn concat(parts:&[&[u8]])->Vec<u8> {
    let mut a=Vec::with_capacity(parts.iter().map(|p|p.len()).sum());
    for p in parts {a.extend_from_slice(p);}
    a
}

/// Answers every read with the next pre-drawn transcript coin; optionally
/// records (address, answer).
struct CoinState { coins:Vec<[u8;32]>, next:usize, record:Option<Table>, collision:bool }
#[derive(Clone,Copy)]
struct CoinOracle<'a>(&'a RefCell<CoinState>);
impl Digest32 for CoinOracle<'_> {
    fn digest(&self,parts:&[&[u8]])->[u8;32] {
        let mut s=self.0.borrow_mut();
        let answer=*s.coins.get(s.next).unwrap_or(&[0;32]);
        s.next+=1;
        if let Some(t)=s.record.as_mut() {
            if let Some(prev)=t.insert(concat(parts),answer) { if prev!=answer {s.collision=true;} }
        }
        answer
    }
}

fn reference(mut s:CoinState,parts:&[&[u8]])->([u8;32],CoinState) {
 let answer=if s.next<s.coins.len() {s.coins[s.next]} else {[0;32]};
 let next=s.next+1;
 let (record,collision)=match s.record {
  None=>(None,s.collision),
  Some(mut t)=>{
   let old=t.previous;
   let key=concat(parts);
   t.previous=Some(answer);t.written=Some((key,answer));
   (Some(t),s.collision || old.map(|v|v!=answer).unwrap_or(false))
  }
 };
 s.next=next;s.record=record;s.collision=collision;(answer,s)
}
#[cfg(kani)]
mod proofs {
 use super::*;
 fn check<const N:usize>() {
  let coins:[[u8;32];2]=kani::any();let len:usize=N;
  let next:usize=kani::any();kani::assume(next<usize::MAX);
  let previous:Option<[u8;32]>=kani::any();let recording:bool=kani::any();let collision:bool=kani::any();
  let bytes:[u8;1]=kani::any();let parts:[&[u8];1]=[&bytes];
  let table=if recording {Some(Table{previous,written:None})} else {None};
  let a=CoinState{coins:coins[..len].to_vec(),next,record:table.clone(),collision};
  let b=CoinState{coins:coins[..len].to_vec(),next,record:table,collision};
  let heap=RefCell::new(a);let digest=CoinOracle(&heap).digest(&parts);
  let (expected,result)=reference(b,&parts);let actual=heap.into_inner();
  assert_eq!(digest,expected);assert_eq!(actual.next,result.next);
  assert_eq!(actual.coins.len(),result.coins.len());
  for i in 0..N {for j in 0..32 {assert_eq!(actual.coins[i][j],result.coins[i][j]);}}assert_eq!(actual.record,result.record);
  assert_eq!(actual.collision,result.collision);
 }
 #[kani::proof] #[kani::unwind(36)] fn call_empty(){check::<0>()}
 #[kani::proof] #[kani::unwind(36)] fn call_one(){check::<1>()}
 #[kani::proof] #[kani::unwind(36)] fn call_two(){check::<2>()}
}
