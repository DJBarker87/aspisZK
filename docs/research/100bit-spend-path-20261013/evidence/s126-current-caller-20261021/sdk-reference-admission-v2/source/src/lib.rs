#![allow(dead_code,unexpected_cfgs)]
use aspis_r1_cost_probe::{verifier,transport::Variant};
use aspis_statement::pool_v1::{PoolV1PairForestTerminalStatementV1,POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,decode_pool_v1_pair_forest_terminal_statement_v1,validate_pool_v1_pair_forest_terminal_statement_v1,encode_pool_v1_pair_verified_afterstate_v1};
use solana_program::{program_error::ProgramError,entrypoint::ProgramResult,hash::hashv,msg};
#[derive(Clone,Copy)] struct SolanaDigest;
impl aspis_core::Digest32 for SolanaDigest {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {hashv(parts).to_bytes()}
}
// The exact cfg-off observer body. Error logging remains a distinct child.
fn observer()->verifier::Observer {None}
fn error(e:verifier::Error)->ProgramError{msg!("r1:error:{:?}",e);ProgramError::InvalidInstructionData}
fn first_decoded(public:aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize)->Result<Vec<u8>,ProgramError>{
    verifier::tx1(public,public_bytes,proof,k,SolanaDigest,observer()).map_err(error)
}
fn decode_public_statement_box(
    bytes: &[u8],
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_forest_terminal_statement_v1(bytes)
            .map_err(|_| ProgramError::InvalidAccountData)?,
    ))
}


use solana_program::{account_info::AccountInfo,pubkey::Pubkey};
use aspis_statement::pool_v1::{PoolV1PairForestTerminalCommonV1,PoolV1PrivateTransferPublicV1,PoolV1WithdrawalPublicV1,PoolV1PairVerifiedAfterstateV1,PoolV1PairForestTerminalFormatErrorV1,PoolV1PairVerifierTransportErrorV1};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
mod adapter {use super::*;
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
pub fn run(program:&Pubkey,accounts:&[AccountInfo<'_>],data:&[u8])->ProgramResult {stage1(program,accounts,data)}
}

#[cfg(kani)] mod proofs {
use super::*;
use aspis_s126_owned_sdk_borrowed as owned;
use owned::{OwnedAccount,OwnedDataCell,OwnedLamportsCell,OwnedSdk};
static mut HITS:u8=0;
static mut PUBLIC_PTR:*const u8=core::ptr::null();
fn planned_decode(bytes:&[u8])->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>{
 assert_eq!(bytes.len(),1880,"reference reaches decoder on original public length");
 assert_eq!(bytes.as_ptr(),unsafe{PUBLIC_PTR},"reference reaches decoder on original public allocation");
 unsafe{HITS+=1;}
 Err(ProgramError::InvalidAccountData)
}
fn planned_scan(_: &[u8])->bool{false}
fn unreachable_first(_:Public<'_>,_:&[u8],_:&[u8],_:usize)->Result<Vec<u8>,ProgramError>{panic!("decoder-error prefix cannot reach first")}
fn unreachable_validate(_:&PoolV1PairForestTerminalStatementV1)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{panic!("decoder-error prefix cannot reach validator")}
fn unreachable_encode(_:&PoolV1PairVerifiedAfterstateV1)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{panic!("decoder-error prefix cannot reach encoder")}
#[kani::proof] #[kani::unwind(48)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::decode_public_statement_box,planned_decode)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::owned_checkpoint_nonzero,planned_scan)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::first_decoded,unreachable_first)]
#[kani::stub(aspis_statement::pool_v1::validate_pool_v1_pair_forest_terminal_statement_v1,unreachable_validate)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_verified_afterstate_v1,unreachable_encode)]
fn reference_admission(){
 let program:[u8;32]=kani::any();let keys:[[u8;32];3]=kani::any();
 let owners:[[u8;32];3]=kani::any();let flags:[[bool;3];3]=kani::any();let rents:[u64;3]=kani::any();
 let split:u8=kani::any();kani::assume(split==10 || split==11);
 kani::assume(keys[0]!=keys[1] && keys[0]!=keys[2] && keys[1]!=keys[2]);
 kani::assume(!flags[0][0] && !flags[0][1] && !flags[0][2]);
 kani::assume(!flags[1][0] && !flags[1][1] && !flags[1][2]);
 kani::assume(owners[2]==program && !flags[2][0] && flags[2][1] && !flags[2][2]);
 let buffers=[kani::vec::exact_vec::<u8,58295>(),kani::vec::exact_vec::<u8,1880>(),kani::vec::exact_vec::<u8,1768>()];
 let pointers=core::array::from_fn::<_,3,_>(|i|buffers[i].as_ptr());
 let proof_slot:usize=kani::any();kani::assume(proof_slot<3);let data_slots=[proof_slot,1,2];
 let lamport_slots:[usize;3]=kani::any();for i in 0..3{kani::assume(lamport_slots[i]<3);}
 let counts:[isize;3]=kani::any();kani::assume(counts[2]==0);kani::assume(counts[1]>=0 && counts[1]<isize::MAX);
 let lamport_counts:[isize;3]=kani::any();let rc:[[usize;4];3]=kani::any();
 for i in 0..3{for j in 0..4{kani::assume(rc[i][j]>=1);}}
 let amounts:[u64;3]=kani::any();unsafe{HITS=0;PUBLIC_PTR=pointers[1];}
 let model=OwnedSdk{
  accounts:(0..3).map(|i|OwnedAccount{key:keys[i],owner:owners[i],is_signer:flags[i][0],is_writable:flags[i][1],executable:flags[i][2],rent_epoch:rents[i],data_slot:data_slots[i],lamports_slot:lamport_slots[i]}).collect(),
  data_cells:buffers.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes,borrowed:counts[i],strong:rc[i][0],weak:rc[i][1]-1}).collect(),
  lamports_cells:(0..3).map(|i|OwnedLamportsCell{amount:amounts[i],borrowed:lamport_counts[i],strong:rc[i][2],weak:rc[i][3]-1}).collect(),
 };
 let (result,out)=owned::owned_stage1(program,model,vec![3,split]);
 assert!(matches!(result,Err(ProgramError::InvalidAccountData)),"reference has the exact decoder-cut error");
 assert_eq!(unsafe{HITS},1,"reference reaches decoder exactly once from derived admission facts");
 for i in 0..3{
  assert_eq!(out.data_cells[i].bytes.as_ptr(),pointers[i]);
  assert_eq!(out.data_cells[i].borrowed,counts[i]);
  assert_eq!(out.data_cells[i].strong,rc[i][0]);assert_eq!(out.data_cells[i].weak,rc[i][1]-1);
  assert_eq!(out.lamports_cells[i].amount,amounts[i]);assert_eq!(out.lamports_cells[i].borrowed,lamport_counts[i]);
  assert_eq!(out.lamports_cells[i].strong,rc[i][2]);assert_eq!(out.lamports_cells[i].weak,rc[i][3]-1);
 }
 kani::cover!(unsafe{HITS}==1 && counts[0]==isize::MAX,"reference prefix permits saturated proof counter");
 kani::cover!(unsafe{HITS}==1 && proof_slot==2,"reference prefix permits proof/checkpoint alias before proof acquisition");
}
}
