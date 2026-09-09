//! Inactive lifecycle facade. The ASQ8 cryptographic implementation is unchanged.
#![allow(unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,program_error::ProgramError,pubkey::Pubkey};
pub use aspis_verifier::{atomic_payment,verify};
// Compile the pinned lifecycle source directly, without exposing unrelated tags.
#[path="../../../../../programs/aspis-verifier/src/lifecycle.rs"]
mod lifecycle;
solana_program::entrypoint!(entry);
#[cfg(target_os="solana")]
#[global_allocator]
static ALLOC:solana_program::entrypoint::BumpAllocator=solana_program::entrypoint::BumpAllocator{
 start:solana_program::entrypoint::HEAP_START_ADDRESS as usize,len:256*1024};
fn entry(id:&Pubkey,accounts:&[AccountInfo],data:&[u8])->ProgramResult{
 if data.starts_with(b"ASQ8") {
  return aspis_verifier::v7_pair_forest_dispatch::process_v7_pair_forest_asq8_instruction(id,accounts,data);
 }
 if accounts.len()!=2 || data.is_empty(){return Err(ProgramError::InvalidInstructionData)}
 match data[0] {
  0 if data.len()==5 => {
   let len=u32::from_le_bytes(data[1..5].try_into().unwrap());
   if !(688..=688+40282).contains(&len) || accounts[0].data_len()!=40+len as usize {
    return Err(ProgramError::InvalidInstructionData)
   }
   lifecycle::init_proof(id,accounts,len)
  },
  1 if data.len()>=9 => {
   let offset=u32::from_le_bytes(data[1..5].try_into().unwrap());
   let len=u32::from_le_bytes(data[5..9].try_into().unwrap()) as usize;
   if data.len()!=9+len{return Err(ProgramError::InvalidInstructionData)}
   lifecycle::upload_chunk(id,accounts,offset,&data[9..])
  },
  62 if data.len()==1 => lifecycle::finalize_proof(id,accounts),
  64 if data.len()==1 => lifecycle::close_proof(id,accounts),
  _ => Err(ProgramError::InvalidInstructionData)
 }
}
