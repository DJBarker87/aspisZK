#![allow(dead_code, unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,program_error::ProgramError,pubkey::Pubkey};
use aspis_statement::pool_v1::{PoolV1PairForestTerminalStatementV1,PoolV1PairForestTerminalCommonV1,PoolV1PrivateTransferPublicV1,PoolV1WithdrawalPublicV1,PoolV1PairVerifiedAfterstateV1,POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
use std::cell::{Ref,RefMut};
#[derive(Clone,Copy)] struct SolanaDigest;
#[derive(Clone,Copy)] enum Phase { Prepare }
fn observer()->Option<fn(Phase)> {None}
#[derive(Clone,Copy)] enum Variant { S2 }
impl Variant { fn tag(self)->u8 {2} }
const CP:usize=1768;
const PROOF:usize=57607;
#[derive(Clone,Copy)] struct Plan {
 statement:PoolV1PairForestTerminalStatementV1, fail:u8, output:u8, output_len:usize,
 public_ptr:usize,public_len:usize,proof_ptr:usize,k:usize,
}
static mut PLAN:Option<Plan>=None;
static mut CALLS:u8=0;
static mut EXPECT_PTRS:[usize;4]=[0;4];
static mut EXPECT_KIND:u8=0;
fn plan()->Plan {unsafe{PLAN.unwrap()}}
fn decode_public_statement_box(bytes:&[u8])->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError> {
 let p=plan();assert_eq!(bytes.as_ptr() as usize,p.public_ptr);assert_eq!(bytes.len(),p.public_len);
 if p.fail==1 {Err(ProgramError::InvalidAccountData)}else{
  let boxed=Box::new(p.statement);
  unsafe {
   EXPECT_PTRS[0]=(&*boxed) as *const _ as usize;
   EXPECT_PTRS[1]=(&boxed.common().lane_transition.candidate_afterstate) as *const _ as usize;
   match boxed.semantic_public() {
    Public::Transfer(a,b)=>{EXPECT_KIND=0;EXPECT_PTRS[2]=a as *const _ as usize;EXPECT_PTRS[3]=b as *const _ as usize;},
    Public::Withdrawal(a,b)=>{EXPECT_KIND=1;EXPECT_PTRS[2]=a as *const _ as usize;EXPECT_PTRS[3]=b as *const _ as usize;},
   }
  }
  Ok(boxed)
 }
}
fn validate_pool_v1_pair_forest_terminal_statement_v1(s:&PoolV1PairForestTerminalStatementV1)->Result<(),()> {
 assert_eq!(s as *const _ as usize,unsafe{EXPECT_PTRS[0]});if plan().fail==2 {Err(())}else{Ok(())}
}
fn encode_pool_v1_pair_verified_afterstate_v1(a:&PoolV1PairVerifiedAfterstateV1)->Result<[u8;688],()> {
 assert_eq!(a as *const _ as usize,unsafe{EXPECT_PTRS[1]});
 if plan().fail==3 {Err(())}else{Ok([0;688])}
}
mod verifier {
 use super::*;
 pub const PROOF_BYTES:usize=PROOF;
 pub fn checkpoint_size(_:Variant)->usize {CP}
 pub fn tx1(public:Public<'_>,bytes:&[u8],proof:&[u8],k:usize,_:SolanaDigest,obs:Option<fn(Phase)>)->Result<Vec<u8>,()> {
  let p=plan();match public {
   Public::Transfer(a,b)=>{assert_eq!(unsafe{EXPECT_KIND},0);assert_eq!(a as *const _ as usize,unsafe{EXPECT_PTRS[2]});assert_eq!(b as *const _ as usize,unsafe{EXPECT_PTRS[3]});},
   Public::Withdrawal(a,b)=>{assert_eq!(unsafe{EXPECT_KIND},1);assert_eq!(a as *const _ as usize,unsafe{EXPECT_PTRS[2]});assert_eq!(b as *const _ as usize,unsafe{EXPECT_PTRS[3]});},
  }
  assert_eq!(bytes.as_ptr() as usize,p.public_ptr);assert_eq!(bytes.len(),p.public_len);
  assert_eq!(proof.as_ptr() as usize,p.proof_ptr+688);assert_eq!(proof.len(),PROOF);
  assert_eq!(k,p.k);assert!(obs.is_none());unsafe{CALLS+=1;}
  if p.fail==4 {Err(())}else{Ok(vec![p.output;p.output_len])}
 }
}
fn error(_:())->ProgramError {ProgramError::InvalidInstructionData}
// Complete frozen first_decoded body; typed verifier boundary above is explicit.
fn first_decoded(public:Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize)->Result<Vec<u8>,ProgramError>{
 verifier::tx1(public,public_bytes,proof,k,SolanaDigest,observer()).map_err(error)
}
