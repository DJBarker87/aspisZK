//! Function-level gates. No unverified row/level/count/batch contract is stubbed.
use core::cell::Cell;
use aspis_core::Digest32;
use super::{adoption_node as observer, p6_callbacks as source, reference as r, frozen as f};

#[derive(Clone, Copy, kani::Arbitrary)]
pub struct Observation { pub digest:[u8;32], pub calls:usize, pub event:u8 }

fn event(left:&[u8],right:&[u8],coordinate:usize)->u8 {
    if coordinate==0 {0x12} else if coordinate<33 {left[coordinate-1]} else {right[coordinate-33]}
}

#[kani::requires(coordinate<65)]
#[kani::ensures(|out:&Observation| out.digest==answer && out.calls==1 && out.event==event(left,right,coordinate))]
pub fn binary_parent(left:&[u8;32],right:&[u8;32],answer:[u8;32],coordinate:usize)->Observation {
    let calls=Cell::new(0);let observed=Cell::new(0);
    let hash=observer::Hash {answer,coordinate,calls:&calls,event:&observed};
    let digest=source::binary_parent(hash,left,right);
    Observation {digest,calls:calls.get(),event:observed.get()}
}

#[kani::requires(index<15 && coordinate<65)]
#[kani::ensures(|out:&Observation| out.digest==answer && out.calls==1 && out.event==event(&values[index],&values[index+1],coordinate))]
pub fn occupied_parent(values:&[[u8;32];16],index:usize,answer:[u8;32],coordinate:usize)->Observation {
    let calls=Cell::new(0);let observed=Cell::new(0);
    let hash=observer::Hash {answer,coordinate,calls:&calls,event:&observed};
    let digest=source::occupied_binary_parent(hash,values,index);
    Observation {digest,calls:calls.get(),event:observed.get()}
}

#[kani::requires(index<16 && sibling.len()==32 && coordinate<65)]
#[kani::ensures(|out:&Observation| out.digest==answer && out.calls==1 && out.event==
    if left {event(&values[index],sibling,coordinate)} else {event(sibling,&values[index],coordinate)})]
pub fn sibling_parent(values:&[[u8;32];16],index:usize,sibling:&[u8],left:bool,answer:[u8;32],coordinate:usize)->Observation {
    let calls=Cell::new(0);let observed=Cell::new(0);
    let hash=observer::Hash {answer,coordinate,calls:&calls,event:&observed};
    let digest=source::sibling_binary_parent(hash,values,index,sibling,left);
    Observation {digest,calls:calls.get(),event:observed.get()}
}

#[kani::proof_for_contract(binary_parent)]
#[kani::stub_verified(observer::hash_parts)]
#[kani::unwind(34)]
fn binary_parent_contract() {
    let left=kani::any();let right=kani::any();
    let coordinate:usize=kani::any();kani::assume(coordinate<65);
    binary_parent(&left,&right,kani::any(),coordinate);
}

#[kani::proof_for_contract(occupied_parent)]
#[kani::stub_verified(observer::hash_parts)]
#[kani::unwind(34)]
fn occupied_parent_contract() {
    let values=kani::any();let index:usize=kani::any();let coordinate:usize=kani::any();
    kani::assume(index<15 && coordinate<65);
    occupied_parent(&values,index,kani::any(),coordinate);
}

#[kani::proof_for_contract(sibling_parent)]
#[kani::stub_verified(observer::hash_parts)]
#[kani::unwind(34)]
fn sibling_parent_contract() {
    let values=kani::any();let sibling:[u8;32]=kani::any();
    let index:usize=kani::any();let coordinate:usize=kani::any();
    kani::assume(index<16 && coordinate<65);
    sibling_parent(&values,index,&sibling,kani::any(),kani::any(),coordinate);
}

/// Independent oracle replies at every ordinal; observe any address byte at
/// any ordinal, the exact number of calls, Bool and arbitrary scratch bytes.
/// This is a bounded complete-function attempt, not a verified certificate
/// until its solver result and unwinding assertions have both passed.
#[derive(Clone,Copy)]
struct TapeHash<'a> {
    answers:&'a [u8;9216],selected:usize,coordinate:usize,
    calls:&'a Cell<usize>,observed:&'a Cell<u8>,
}
impl Digest32 for TapeHash<'_> {
    fn digest(&self,parts:&[&[u8]])->[u8;32] {
        assert_eq!(parts.len(),3);assert_eq!(parts[0].len(),1);
        assert_eq!(parts[1].len(),32);assert_eq!(parts[2].len(),32);
        let call=self.calls.get();assert!(call<288);
        if call==self.selected {
            let c=self.coordinate;
            self.observed.set(if c==0 {parts[0][0]}else if c<33 {parts[1][c-1]}else{parts[2][c-33]});
        }
        self.calls.set(call+1);r::read32(&self.answers[32*call..32*call+32])
    }
}

#[kani::proof]
#[kani::stub_verified(r::read32)]
#[kani::unwind(34)]
fn verify_in_place_complete() {
    let idx:[u32;16]=kani::any();let val:[[u8;32];16]=kani::any();
    let n:usize=kani::any();let nodes:[u8;5504]=kani::any();
    let length:usize=kani::any();kani::assume(length<=5504);
    // Primitive-byte Arbitrary avoids generic nested-array initialization.
    // The verified read32 contract recovers each independent 32-byte reply.
    let root:[u8;32]=kani::any();let answers:[u8;9216]=kani::any();
    let selected:usize=kani::any();let coordinate:usize=kani::any();
    kani::assume(selected<288 && coordinate<65);
    let calls=Cell::new(0);let observed=Cell::new(0);
    let hash=TapeHash{answers:&answers,selected,coordinate,calls:&calls,observed:&observed};
    let mut source_idx=idx;let mut source_val=val;
    let source_ok=f::multiproof::verify_in_place(hash,f::multiproof::Arity::Two,&root,
        &mut source_idx,&mut source_val,n,&nodes[..length]);
    let source_calls=calls.get();let source_event=observed.get();
    calls.set(0);observed.set(0);
    let (reference_ok,reference)=r::verify_owned(hash,root,r::Scratch{idx,val,n,at:0},&nodes[..length]);
    assert_eq!(source_ok,reference_ok);assert_eq!(source_calls,calls.get());
    assert_eq!(source_event,observed.get());
    let j:usize=kani::any();let k:usize=kani::any();kani::assume(j<16 && k<32);
    assert_eq!(source_idx[j],reference.idx[j]);assert_eq!(source_val[j][k],reference.val[j][k]);
}
