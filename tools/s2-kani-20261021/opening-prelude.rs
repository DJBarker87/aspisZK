#![allow(dead_code,private_interfaces,static_mut_refs)]
#[derive(Clone,Copy)] struct Hash;
trait Digest32:Copy {} impl Digest32 for Hash {}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct E(u32);
impl E {const ZERO:Self=Self(0);fn to_le_bytes(self)->[u8;32]{unsafe{INACTIVE}}}
type K=u32;type SecureCirclePoint=u8;
#[derive(Clone,Copy,Debug,PartialEq,Eq)] enum Variant {S2}
impl Variant {fn folds(self)->usize{2}}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] enum Error {Transcript,Relation}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct Event{row:u8,len:usize,byte:u8,gamma:bool,ptr:usize,before:[u8;32]}
const EMPTY:Event=Event{row:0,len:0,byte:0,gamma:false,ptr:0,before:[0;32]};
static mut EVENTS:[Event;6]=[EMPTY;6];static mut COUNT:usize=0;static mut PROBE:usize=0;
static mut INACTIVE:[u8;32]=[0;32];static mut FAIL:bool=false;
static mut VALUES:[u32;6]=[0;6];static mut STATES:[[u8;32];6]=[[0;32];6];static mut CLAIM_FAIL:bool=false;
static mut QUERIES:[u32;22]=[0;22];
fn observe(row:u8,payload:&[u8],gamma:bool,before:[u8;32]){unsafe{
EVENTS[COUNT]=Event{row,len:payload.len(),byte:if PROBE<payload.len(){payload[PROBE]}else{0},gamma,ptr:if row==27||row==29||row==31{payload.as_ptr()as usize}else{0},before};COUNT+=1;
}}
struct Transcript<H>{state:[u8;32],_hash:H}
impl<H:Digest32> Transcript<H>{
fn new(hash:H,state:[u8;32],_:Variant)->Self{Self{state,_hash:hash}}
fn state(&self)->[u8;32]{self.state}
fn scalar(&mut self,row:u8,payload:&[u8],gamma:bool)->E{observe(row,payload,gamma,self.state);self.state=unsafe{STATES[(row-27)as usize]};E(unsafe{VALUES[(row-27)as usize]})}
fn queries(&mut self,row:u8,payload:&[u8])->Result<[u32;22],Error>{observe(row,payload,false,self.state);self.state=unsafe{STATES[(row-27)as usize]};if unsafe{FAIL}{Err(Error::Transcript)}else{Ok(unsafe{QUERIES})}}
fn scalar_k(&mut self,row:u8,payload:&[u8])->K{observe(row,payload,false,self.state);self.state=unsafe{STATES[(row-27)as usize]};unsafe{VALUES[5]}}
}
mod r1_semantic {use super::*;pub struct Verified<H>{pub transcript:Transcript<H>,pub roots:[[u8;32];2],pub alpha:[K;10],pub z:[SecureCirclePoint;2]}}
struct View<'a>{variant:Variant,y1:&'a[u8],inactive:E,round0:&'a[u8],folded_root:Option<&'a[u8;32]>,round1:&'a[u8],final_message:&'a[u8]}
fn powers<const N:usize>(x:E)->[E;N]{[x;N]}
fn prepared_claim<H:Digest32>(_:&r1_semantic::Verified<H>,_:&[u8],_:E,_:&[E;29],kappa:E)->Result<E,Error>{if unsafe{CLAIM_FAIL}{Err(Error::Relation)}else{Ok(kappa)}}
