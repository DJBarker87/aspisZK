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

#[path="effect.rs"] mod effect;
impl effect::Recording for Table {
 fn insert(mut self,parts:&[&[u8]],answer:[u8;32])->(Option<[u8;32]>,Self) {
  let previous=Table::insert(&mut self,concat(parts),answer);(previous,self)
 }
}
fn reference(s:CoinState,parts:&[&[u8]])->([u8;32],CoinState) {
 let state=effect::CoinState{coins:s.coins,next:s.next,record:s.record,collision:s.collision};
 let (answer,s)=<effect::CoinOracle as effect::EffectDigest32<_>>::digest(state,parts);
 (answer,CoinState{coins:s.coins,next:s.next,record:s.record,collision:s.collision})
}

#[cfg(kani)]
mod proofs {
 use super::*;
 fn check<const N:usize>() {
  let coins:[[u8;32];N]=kani::any();let len:usize=N;
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
  if N>0 {let i:usize=kani::any();kani::assume(i<N);let j:usize=kani::any();kani::assume(j<32);assert_eq!(actual.coins[i][j],result.coins[i][j]);}assert_eq!(actual.record,result.record);
  assert_eq!(actual.collision,result.collision);
 }
 #[kani::proof] #[kani::stub_verified(effect::different)] #[kani::unwind(36)] fn call_empty(){check::<0>()}
 #[kani::proof] #[kani::stub_verified(effect::different)] #[kani::unwind(36)] fn call_one(){check::<1>()}
 #[kani::proof] #[kani::stub_verified(effect::different)] #[kani::unwind(36)] fn call_two(){check::<2>()}
 #[kani::proof_for_contract(effect::different)]
 #[kani::unwind(36)]
 fn different_contract(){effect::different(kani::any(),kani::any());}
 #[kani::proof] #[kani::stub_verified(effect::different)] #[kani::unwind(116)]
 fn call_native115(){check::<115>()}
 // Shared immutable input isolates the exact source get/default cell from
 // RefCell, recording and the duplicated 115-word heap constructions.
 #[kani::proof] #[kani::unwind(116)]
 fn read_native115(){
  let data:[[u8;32];115]=kani::any();let coins=data.to_vec();
  let next:usize=kani::any();let at:usize=kani::any();kani::assume(at<32);
  let source=*coins.get(next).unwrap_or(&[0;32]);
  let reference=if next<coins.len(){coins[next]}else{[0;32]};
  assert_eq!(source[at],reference[at]);
 }
}
