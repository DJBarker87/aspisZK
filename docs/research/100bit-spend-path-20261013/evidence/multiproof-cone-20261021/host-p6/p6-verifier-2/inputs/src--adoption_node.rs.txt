//! Single-node separation cut. The window is arbitrary, NOT a zero-filled
//! replacement for the physical nodes. Physical-slice provenance is a separate
//! obligation; these certificates never claim a whole-slot implementation join.
use core::cell::Cell;
use aspis_core::Digest32;
use super::{frozen as f,reference as r};

#[derive(Clone,Copy,kani::Arbitrary)]
pub struct HashObservation { pub digest:[u8;32], pub event:u8, pub calls:usize }
#[kani::requires(parts.len()==3 && parts[0].len()==1 && parts[1].len()==32 && parts[2].len()==32 && coordinate<65)]
#[kani::ensures(|out:&HashObservation| out.digest==answer && out.calls==1 && out.event==
 if coordinate==0 {parts[0][0]} else if coordinate<33 {parts[1][coordinate-1]} else {parts[2][coordinate-33]})]
pub fn hash_parts(parts:&[&[u8]],answer:[u8;32],coordinate:usize)->HashObservation {
 HashObservation {digest:answer,calls:1,event:if coordinate==0 {parts[0][0]} else if coordinate<33 {parts[1][coordinate-1]} else {parts[2][coordinate-33]}}
}
#[derive(Clone,Copy)]
pub struct Hash<'a> {pub answer:[u8;32],pub coordinate:usize,pub calls:&'a Cell<usize>,pub event:&'a Cell<u8>}
impl Digest32 for Hash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  assert_eq!(parts.len(),3);assert_eq!(parts[0].len(),1);
  assert_eq!(parts[1].len(),32);assert_eq!(parts[2].len(),32);
  let out=hash_parts(parts,self.answer,self.coordinate);
  self.calls.set(self.calls.get()+out.calls);self.event.set(out.event);out.digest
 }
}
/// Exact binary_group on a separated window. at is relative to the window;
/// translating it back to the physical slice needs the window/frame theorem.
pub fn source<H:Digest32>(hash:H,s:r::Scratch,window:&[u8],i:usize,w:usize)->(bool,r::Scratch,usize,usize) {
 let (mut idx,mut val,mut at,mut next_i,mut next_w)=(s.idx,s.val,s.at,i,w);
 let success=f::multiproof::binary_group(hash,&mut idx,&mut val,s.n,window,&mut at,&mut next_w,&mut next_i);
 (success,r::Scratch{idx,val,n:s.n,at},next_i,next_w)
}
