//! Proof-only observer wrappers. Cells are local to a call; no global oracle
//! state is erased by a function contract. All protocol effects are returned.
use core::cell::Cell;
use aspis_core::Digest32;
use super::{frozen as f,reference as r};

#[derive(Clone,Copy)]
pub struct LeafObservation {pub digest:[u8;32],pub calls:usize,pub event:u8}
#[derive(Clone,Copy)]
struct LeafHash<'a> {tree:usize,coordinate:usize,answer:[u8;32],calls:&'a Cell<usize>,event:&'a Cell<u8>}
impl Digest32 for LeafHash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  let width=if self.tree==0 {480}else{128};
  assert_eq!(parts.len(),3);assert_eq!(parts[0].len(),2);
  assert_eq!(parts[1].len(),width);assert_eq!(parts[2].len(),32);
  self.calls.set(self.calls.get()+1);
  let c=self.coordinate;
  self.event.set(if c<2 {parts[0][c]}else if c<2+width {parts[1][c-2]}else{parts[2][c-2-width]});
  self.answer
 }
}
pub fn leaf_event(tree:usize,q:&[u8;832],coordinate:usize)->u8 {
 let (tag,start,width,salt)=if tree==0 {(0x71,0,480,608)}else if tree==1 {(0xf1,480,128,640)}else{(0x72,672,128,800)};
 if coordinate==0 {0x10}else if coordinate==1 {tag}else if coordinate<2+width {q[start+coordinate-2]}else{q[salt+coordinate-2-width]}
}
#[kani::requires(tree<3)]
#[kani::requires(coordinate<2+(if tree==0 {480}else{128})+32)]
#[kani::ensures(|out:&LeafObservation| out.digest==answer && out.calls==1 && out.event==leaf_event(tree,q,coordinate))]
pub fn leaf_hash(tree:usize,q:&[u8;832],answer:[u8;32],coordinate:usize)->LeafObservation {
 let calls=Cell::new(0);let event=Cell::new(0);
 let digest=f::batch::batch_leaf(LeafHash{tree,coordinate,answer,calls:&calls,event:&event},tree,q);
 LeafObservation{digest,calls:calls.get(),event:event.get()}
}

#[derive(Clone,Copy)]
pub struct BinaryHash<'a> {
 pub answers:&'a [[u8;32];16],pub selected:usize,pub coordinate:usize,
 pub calls:&'a Cell<usize>,pub event:&'a Cell<u8>,
}
impl Digest32 for BinaryHash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  assert_eq!(parts.len(),3);assert_eq!(parts[0].len(),1);
  assert_eq!(parts[1].len(),32);assert_eq!(parts[2].len(),32);
  let call=self.calls.get();assert!(call<16);
  if call==self.selected {
   let c=self.coordinate;
   self.event.set(if c==0 {parts[0][0]}else if c<33 {parts[1][c-1]}else{parts[2][c-33]});
  }
  self.calls.set(call+1);self.answers[call]
 }
}

// Only used by harnesses, with arbitrary independent observation coordinates.
pub fn same_scratch(a:&r::Scratch,b:&r::Scratch) {
 let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16 && k<32);
 assert_eq!(a.idx[j],b.idx[j]);assert_eq!(a.val[j][k],b.val[j][k]);
 assert_eq!(a.n,b.n);assert_eq!(a.at,b.at);
}
