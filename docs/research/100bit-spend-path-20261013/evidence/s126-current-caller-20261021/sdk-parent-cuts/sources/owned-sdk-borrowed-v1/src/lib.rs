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

#[derive(Clone,Copy)]
pub struct OwnedAccount {
 pub key:[u8;32],pub owner:[u8;32],pub is_signer:bool,pub is_writable:bool,
 pub executable:bool,pub rent_epoch:u64,pub data_slot:usize,pub lamports_slot:usize,
}
pub struct OwnedDataCell {
 pub bytes:Vec<u8>,pub borrowed:isize,pub strong:usize,pub weak:usize,
}
pub struct OwnedLamportsCell {
 pub amount:u64,pub borrowed:isize,pub strong:usize,pub weak:usize,
}
pub struct OwnedSdk {
 pub accounts:Vec<OwnedAccount>,pub data_cells:Vec<OwnedDataCell>,
 pub lamports_cells:Vec<OwnedLamportsCell>,
}
pub struct LiveGuards {
 pub checkpoint:Option<usize>,pub public:Option<usize>,pub proof:Option<usize>,
}

pub fn shared_allowed(counter:isize)->bool {counter>=0 && counter<isize::MAX}
// The real SDK length helper acquires/drops a temporary shared guard.
pub fn owned_data_len(sdk:&OwnedSdk,slot:usize)->Result<usize,ProgramError> {
 if shared_allowed(sdk.data_cells[slot].borrowed) {Ok(sdk.data_cells[slot].bytes.len())}
 else {Err(ProgramError::AccountBorrowFailed)}
}
pub fn owned_acquire_checkpoint(sdk:&mut OwnedSdk,guards:&mut LiveGuards,slot:usize)->ProgramResult {
 if sdk.data_cells[slot].borrowed!=0 {return Err(ProgramError::AccountBorrowFailed);}
 sdk.data_cells[slot].borrowed=-1;
 guards.checkpoint=Some(slot);
 Ok(())
}
pub fn owned_acquire_shared(sdk:&mut OwnedSdk,slot:usize)->ProgramResult {
 let count=sdk.data_cells[slot].borrowed;
 if !shared_allowed(count) {return Err(ProgramError::AccountBorrowFailed);}
 sdk.data_cells[slot].borrowed=count.checked_add(1).unwrap();
 Ok(())
}
pub fn owned_release_guards(sdk:&mut OwnedSdk,guards:LiveGuards) {
 // Reverse acquisition order matches Rust local drop order, including aliases.
 if let Some(slot)=guards.proof {sdk.data_cells[slot].borrowed=sdk.data_cells[slot].borrowed.checked_sub(1).unwrap();}
 if let Some(slot)=guards.public {sdk.data_cells[slot].borrowed=sdk.data_cells[slot].borrowed.checked_sub(1).unwrap();}
 if let Some(slot)=guards.checkpoint {sdk.data_cells[slot].borrowed=sdk.data_cells[slot].borrowed.checked_add(1).unwrap();}
}
pub fn owned_checkpoint_nonzero(bytes:&[u8])->bool {
 let mut i=0;
 while i<bytes.len() {if bytes[i]!=0 {return true;}i+=1;}
 false
}

pub fn owned_stage1_body(program_id:[u8;32],sdk:&mut OwnedSdk,data:&[u8],guards:&mut LiveGuards)->ProgramResult {
 if !(data == &[3,10] || data == &[3,11]) || sdk.accounts.len()!=3 {
  return Err(ProgramError::InvalidInstructionData);
 }
 let proof=sdk.accounts[0];let public=sdk.accounts[1];let checkpoint=sdk.accounts[2];
 // Exact three-key comparison order of require_distinct_accounts on 3 inputs.
 if proof.key==public.key || proof.key==checkpoint.key || public.key==checkpoint.key {
  return Err(ProgramError::InvalidArgument);
 }
 if proof.is_signer || proof.is_writable || proof.executable {return Err(ProgramError::InvalidAccountData);}
 if public.is_signer || public.is_writable || public.executable {return Err(ProgramError::InvalidAccountData);}
 if checkpoint.owner!=program_id || checkpoint.is_signer || checkpoint.executable
  || !checkpoint.is_writable || owned_data_len(sdk,checkpoint.data_slot)?!=verifier::checkpoint_size(Variant::S2) {
  return Err(ProgramError::InvalidAccountData);
 }
 owned_acquire_checkpoint(sdk,guards,checkpoint.data_slot)?;
 if owned_checkpoint_nonzero(&sdk.data_cells[checkpoint.data_slot].bytes) {
  return Err(ProgramError::AccountAlreadyInitialized);
 }
 owned_acquire_shared(sdk,public.data_slot)?;
 guards.public=Some(public.data_slot);
 let statement={
  let public_data=&sdk.data_cells[public.data_slot].bytes;
  decode_public_statement_box(public_data)
 }?;
 validate_pool_v1_pair_forest_terminal_statement_v1(&statement).map_err(|_|ProgramError::InvalidAccountData)?;
 let candidate=encode_pool_v1_pair_verified_afterstate_v1(&statement.common().lane_transition.candidate_afterstate)
  .map_err(|_|ProgramError::InvalidAccountData)?;
 owned_acquire_shared(sdk,proof.data_slot)?;
 guards.proof=Some(proof.data_slot);
 let public_data=&sdk.data_cells[public.data_slot].bytes;
 let proof_data=&sdk.data_cells[proof.data_slot].bytes;
 let proof_length=verifier::PROOF_BYTES;
 let proof_start=POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
 let proof_end=proof_start.checked_add(proof_length).ok_or(ProgramError::InvalidAccountData)?;
 if proof_data.len()!=proof_end || proof_data[..proof_start]!=candidate || proof_data[proof_start+8]!=Variant::S2.tag() {
  return Err(ProgramError::InvalidAccountData);
 }
 let result=first_decoded(statement.semantic_public(),&public_data,&proof_data[proof_start..proof_end],data[1] as usize)?;
 if result.len()!=sdk.data_cells[checkpoint.data_slot].bytes.len() {return Err(ProgramError::InvalidAccountData);}
 // Owned heap bytes, not an SDK slice descriptor or pointer, are replaced.
 // The actual SDK copy/write frame is a separate concrete operation certificate.
 sdk.data_cells[checkpoint.data_slot].bytes=result;
 Ok(())
}
pub fn owned_stage1(program_id:[u8;32],mut sdk:OwnedSdk,data:Vec<u8>)->(ProgramResult,OwnedSdk) {
 let mut guards=LiveGuards{checkpoint:None,public:None,proof:None};
 let result=owned_stage1_body(program_id,&mut sdk,&data,&mut guards);
 owned_release_guards(&mut sdk,guards);
 (result,sdk)
}
