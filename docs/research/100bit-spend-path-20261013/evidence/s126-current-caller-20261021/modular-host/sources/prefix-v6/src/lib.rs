#![allow(dead_code, unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,program_error::ProgramError,pubkey::Pubkey};
use aspis_statement::pool_v1::{PoolV1PairForestTerminalStatementV1,PoolV1PairForestTerminalCommonV1,PoolV1PrivateTransferPublicV1,PoolV1WithdrawalPublicV1,PoolV1PairVerifiedAfterstateV1,POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
use std::cell::{Ref,RefMut};
#[derive(Clone,Copy)] struct SolanaDigest;
#[derive(Clone,Copy)] enum Phase {Parsed,Semantic,SemanticPart(u8),Prepare,CheckpointRead,Merkle(usize),Query(usize),QueryPart(usize,u8),CheckpointWrite,Relation,Final}
fn observer()->Option<fn(Phase)> {None}
#[derive(Clone,Copy)] enum Variant {S1,S2,D}
impl Variant { fn tag(self)->u8 {match self {Self::S1=>1,Self::S2=>2,Self::D=>3}} }
const CP:usize=1768;
const PROOF:usize=57607;
#[derive(Clone,Copy)] struct Plan {
 fail:u8, output:u8, output_len:usize,
 public_ptr:*const u8,public_len:usize,proof_ptr:*const u8,k:usize,
}
static mut PLAN:Option<Plan>=None;
static mut STATEMENT:Option<PoolV1PairForestTerminalStatementV1>=None;
static mut CALLS:u8=0;
static mut EXPECT_PTRS:[*const ();4]=[core::ptr::null();4];
static mut EXPECT_KIND:u8=0;
fn plan()->Plan {unsafe{PLAN.unwrap()}}
fn decode_public_statement_box(bytes:&[u8])->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError> {
 let p=plan();assert_eq!(bytes.as_ptr(),p.public_ptr);assert_eq!(bytes.len(),p.public_len);
 if p.fail==1 {Err(ProgramError::InvalidAccountData)}else{
  let boxed=Box::new(unsafe{STATEMENT.take().unwrap()});
  unsafe {
   EXPECT_PTRS[0]=(&*boxed) as *const _ as *const ();
   EXPECT_PTRS[1]=(&boxed.common().lane_transition.candidate_afterstate) as *const _ as *const ();
   match boxed.semantic_public() {
    Public::Transfer(a,b)=>{EXPECT_KIND=0;EXPECT_PTRS[2]=a as *const _ as *const ();EXPECT_PTRS[3]=b as *const _ as *const ();},
    Public::Withdrawal(a,b)=>{EXPECT_KIND=1;EXPECT_PTRS[2]=a as *const _ as *const ();EXPECT_PTRS[3]=b as *const _ as *const ();},
   }
  }
  Ok(boxed)
 }
}
fn validate_pool_v1_pair_forest_terminal_statement_v1(s:&PoolV1PairForestTerminalStatementV1)->Result<(),()> {
 assert_eq!(s as *const _ as *const (),unsafe{EXPECT_PTRS[0]});if plan().fail==2 {Err(())}else{Ok(())}
}
fn encode_pool_v1_pair_verified_afterstate_v1(a:&PoolV1PairVerifiedAfterstateV1)->Result<[u8;688],()> {
 assert_eq!(a as *const _ as *const (),unsafe{EXPECT_PTRS[1]});
 if plan().fail==3 {Err(())}else{Ok([0;688])}
}
mod verifier {
 use super::*;
 pub const PROOF_BYTES:usize=PROOF;
 pub fn checkpoint_size(_:Variant)->usize {CP}
 pub fn tx1(public:Public<'_>,bytes:&[u8],proof:&[u8],k:usize,_:SolanaDigest,obs:Option<fn(Phase)>)->Result<Vec<u8>,()> {
  let p=plan();match public {
   Public::Transfer(a,b)=>{assert_eq!(unsafe{EXPECT_KIND},0);assert_eq!(a as *const _ as *const (),unsafe{EXPECT_PTRS[2]});assert_eq!(b as *const _ as *const (),unsafe{EXPECT_PTRS[3]});},
   Public::Withdrawal(a,b)=>{assert_eq!(unsafe{EXPECT_KIND},1);assert_eq!(a as *const _ as *const (),unsafe{EXPECT_PTRS[2]});assert_eq!(b as *const _ as *const (),unsafe{EXPECT_PTRS[3]});},
  }
  assert_eq!(bytes.as_ptr(),p.public_ptr);assert_eq!(bytes.len(),p.public_len);
  assert_eq!(proof.as_ptr(),unsafe{p.proof_ptr.add(688)});assert_eq!(proof.len(),PROOF);
  assert_eq!(k,p.k);assert!(obs.is_none());unsafe{CALLS+=1;}
  // Prefix certificate: argument assertions above occur before this return.
  Err(())
 }
}
fn error(_:())->ProgramError {ProgramError::InvalidInstructionData}
// Complete frozen first_decoded body; typed verifier boundary above is explicit.
fn first_decoded(public:Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize)->Result<Vec<u8>,ProgramError>{
 verifier::tx1(public,public_bytes,proof,k,SolanaDigest,observer()).map_err(error)
}

mod adapter {
use super::*;
fn readonly_buffer_meta_ok(
    is_signer: bool,
    is_writable: bool,
    executable: bool,
) -> ProgramResult {
    if is_signer || is_writable || executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

fn require_readonly_buffer(account: &AccountInfo<'_>) -> ProgramResult {
    readonly_buffer_meta_ok(account.is_signer, account.is_writable, account.executable)
}

fn require_verifier_checkpoint(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    writable: bool,
) -> ProgramResult {
    if account.owner != program_id || account.is_signer || account.executable
        || account.is_writable != writable
        || account.try_data_len()? != verifier::checkpoint_size(Variant::S2)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

fn require_distinct_accounts<const N: usize>(accounts: &[&AccountInfo<'_>; N]) -> ProgramResult {
    for (index, account) in accounts.iter().enumerate() {
        if accounts[..index]
            .iter()
            .any(|previous| previous.key == account.key)
        {
            return Err(ProgramError::InvalidArgument);
        }
    }
    Ok(())
}

fn stage1(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult {
    if !(data == &[3, 10] || data == &[3, 11]) || accounts.len() != 3 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let proof_account = &accounts[0];
    let public_account = &accounts[1];
    let checkpoint_account = &accounts[2];
    require_distinct_accounts(&[proof_account, public_account, checkpoint_account])?;
    require_readonly_buffer(proof_account)?;
    require_readonly_buffer(public_account)?;
    require_verifier_checkpoint(checkpoint_account, program_id, true)?;
    let mut checkpoint_data = checkpoint_account.try_borrow_mut_data()?;
    if checkpoint_data.iter().any(|byte| *byte != 0) {
        return Err(ProgramError::AccountAlreadyInitialized);
    }
    let public_data = public_account.try_borrow_data()?;
    let statement = decode_public_statement_box(&public_data)?;
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let candidate = encode_pool_v1_pair_verified_afterstate_v1(
        &statement.common().lane_transition.candidate_afterstate,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;

    let proof_data = proof_account.try_borrow_data()?;
    let proof_length = verifier::PROOF_BYTES;
    let proof_start = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let proof_end = proof_start.checked_add(proof_length)
        .ok_or(ProgramError::InvalidAccountData)?;
    if proof_data.len() != proof_end
        || proof_data[..proof_start] != candidate
        || proof_data[proof_start + 8] != Variant::S2.tag()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let checkpoint = super::first_decoded(statement.semantic_public(), &public_data, &proof_data[proof_start..proof_end], data[1] as usize)?;
    if checkpoint.len() != checkpoint_data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    checkpoint_data.copy_from_slice(&checkpoint);
    #[cfg(feature="cu-profiling")]
    {
    msg!("r1:pool-adapter-stage1-checkpoint-written");
    solana_program::log::sol_log_compute_units();
    }
    Ok(())
}
pub fn run(p:&Pubkey,a:&[AccountInfo],d:&[u8])->ProgramResult {stage1(p,a,d)}
}
#[cfg(kani)] mod proofs {
use super::*;
fn statement()->PoolV1PairForestTerminalStatementV1 {
 // Every bit pattern is valid for these three reference-free, enum-free
 // structs (only u8/u32/u64, M31(u32), fixed arrays and their structs).
 let common:PoolV1PairForestTerminalCommonV1=unsafe{std::mem::transmute(kani::any::<[u8;std::mem::size_of::<PoolV1PairForestTerminalCommonV1>()]>())};
 if kani::any() {
  let public:PoolV1PrivateTransferPublicV1=unsafe{std::mem::transmute(kani::any::<[u8;std::mem::size_of::<PoolV1PrivateTransferPublicV1>()]>())};
  PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public}
 } else {
  let public:PoolV1WithdrawalPublicV1=unsafe{std::mem::transmute(kani::any::<[u8;std::mem::size_of::<PoolV1WithdrawalPublicV1>()]>())};
  PoolV1PairForestTerminalStatementV1::Withdrawal{common,public}
 }
}
#[kani::proof]
#[kani::unwind(1772)]
fn actual_sdk_stage1_prefix_binding() {
 let program=Pubkey::new_from_array([4;32]);
 let keys:[Pubkey;3]=[Pubkey::new_from_array([1;32]),Pubkey::new_from_array([2;32]),Pubkey::new_from_array([3;32])];
 let owner=Pubkey::new_from_array([5;32]);
 let mut lamports=[0u64;3];
 let [ref mut l0,ref mut l1,ref mut l2]=lamports;
 // One arbitrary selected cell covers the byte-oblivious SDK/control spine;
 // this harness does not claim an all-byte parser/validator certificate.
 let mut proof:[u8;688+PROOF]=kani::any();
 let mut public:[u8;1880]=kani::any();
 let mut checkpoint:[u8;CP]=kani::any();
 let observed:usize=kani::any();kani::assume(observed<CP);
 let before=checkpoint[observed];
 let proof_ptr=proof.as_ptr();let public_ptr=public.as_ptr();
 let p=Plan{fail:kani::any(),output:kani::any(),output_len:if kani::any(){CP}else{0},public_ptr,public_len:public.len(),proof_ptr,k:if kani::any(){10}else{11}};
 unsafe{PLAN=Some(p);STATEMENT=Some(statement());CALLS=0;}
 let a0=AccountInfo::new(&keys[0],false,false,l0,&mut proof,&owner,false,0);
 let a1=AccountInfo::new(&keys[1],false,false,l1,&mut public,&owner,false,0);
 let a2=AccountInfo::new(&keys[2],false,true,l2,&mut checkpoint,&program,false,0);
 let accounts=[a0,a1,a2];
 // Live immutable or mutable borrows exercise real RefCell rejection,
 // with guards retained until after the actual full stage1 call.
 let held_shared:Option<Ref<'_,&mut [u8]>>=if kani::any(){Some(accounts[2].try_borrow_data().unwrap())}else{None};
 let held_mut:Option<RefMut<'_,&mut [u8]>>=if kani::any(){Some(accounts[1].try_borrow_mut_data().unwrap())}else{None};
 let data=[3,p.k as u8];
 let result=adapter::run(&program,&accounts,&data);
 drop(held_shared);drop(held_mut);
 let after=accounts[2].try_borrow_data().unwrap();
 assert!(result.is_err());assert_eq!(after[observed],before);
 assert!(unsafe{CALLS}<=1);kani::cover!(unsafe{CALLS}==1);
 assert!(accounts[0].try_borrow_mut_data().is_ok());
 assert!(accounts[1].try_borrow_mut_data().is_ok());
 drop(after);assert!(accounts[2].try_borrow_mut_data().is_ok());
}
#[kani::proof]
#[kani::unwind(20)]
fn sdk_immutable_alias_and_writeback() {
 let key=Pubkey::new_from_array([1;32]);let owner=Pubkey::new_from_array([2;32]);
 let mut lamports=0;let mut data:[u8;16]=kani::any();let original=data;
 let account=AccountInfo::new(&key,false,false,&mut lamports,&mut data,&owner,false,0);
 let alias=account.clone();
 let reader=account.try_borrow_data().unwrap();
 assert!(matches!(alias.try_borrow_mut_data(),Err(ProgramError::AccountBorrowFailed)));
 assert_eq!(&**reader,&original[..]);
 let reader2=alias.try_borrow_data().unwrap();assert_eq!(reader.as_ptr(),reader2.as_ptr());
 drop(reader2);drop(reader);
 let replacement:[u8;16]=kani::any();
 let mut writer=alias.try_borrow_mut_data().unwrap();
 assert!(matches!(account.try_borrow_data(),Err(ProgramError::AccountBorrowFailed)));
 writer.copy_from_slice(&replacement);drop(writer);
 assert_eq!(&**account.try_borrow_data().unwrap(),&replacement[..]);
}
}
