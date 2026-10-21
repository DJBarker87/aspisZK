#![allow(dead_code,private_interfaces,static_mut_refs)]
#[derive(Clone,Copy)] struct SolanaDigest;
trait Digest32:Copy {}
impl Digest32 for SolanaDigest {}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] enum ProgramError {InvalidInstructionData}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] enum Error {Parse,Backend}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] enum Phase {Parsed}
type Observer=Option<fn(Phase)>;
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct Event {op:u8,a:usize,an:usize,b:usize,bn:usize,c:usize,cn:usize,k:usize,semantic:u32,observer:bool}
const EMPTY:Event=Event{op:0,a:0,an:0,b:0,bn:0,c:0,cn:0,k:0,semantic:0,observer:false};
static mut EVENTS:[Event;3]=[EMPTY;3];
static mut COUNT:usize=0;
static mut FAIL:[bool;3]=[false;3];
fn push(op:u8,a:&[u8],b:&[u8],c:&[u8],k:usize,semantic:u32,observer:bool) {
unsafe {EVENTS[COUNT]=Event{op,a:a.as_ptr() as usize,an:a.len(),b:b.as_ptr() as usize,bn:b.len(),c:c.as_ptr() as usize,cn:c.len(),k,semantic,observer};COUNT+=1;}
}
fn error(_:Error)->ProgramError {ProgramError::InvalidInstructionData}
mod aspis_statement {pub mod pool_v1 {pub mod pair_forest_semantic_terminal {pub mod r0 {
#[derive(Clone,Copy)] pub struct Public<'a>{pub value:u32,pub bytes:&'a [u8]}
}}}}
mod verifier {
use super::*;
pub type Observer=super::Observer;
pub fn tx1(public:aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize,_hash:SolanaDigest,obs:Observer)->Result<Vec<u8>,Error>{
push(1,public_bytes,proof,public.bytes,k,public.value,obs.is_some());
if unsafe {FAIL[2]} {Err(Error::Backend)} else {Ok(Vec::new())}
}
}
fn parse_shape(proof:&[u8])->Result<(),Error>{push(2,proof,&[],&[],0,0,false);if unsafe {FAIL[0]} {Err(Error::Parse)} else {Ok(())}}
fn canonical_scan(proof:&[u8])->Result<(),Error>{push(3,proof,&[],&[],0,0,false);if unsafe {FAIL[1]} {Err(Error::Parse)} else {Ok(())}}
fn mark(obs:Observer,p:Phase){if let Some(f)=obs {f(p)}}
fn tx2_common<H:Copy>(public:&[u8],proof:&[u8],checkpoint:&[u8],_hash:H,obs:Observer)->Result<(),Error>{push(4,public,proof,checkpoint,0,0,obs.is_some());if unsafe {FAIL[2]} {Err(Error::Backend)} else {Ok(())}}
