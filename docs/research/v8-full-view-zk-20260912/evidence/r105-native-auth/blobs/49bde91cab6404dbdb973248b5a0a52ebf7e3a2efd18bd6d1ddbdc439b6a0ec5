//! Authentication ONLY. Acceptance here is NEVER Aspis proof acceptance.
extern crate aspis_core as corelib;
use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,
    program_error::ProgramError,pubkey::Pubkey};
mod r95_merkle;
mod r101_merkle;
solana_program::entrypoint!(entry);
#[cfg(target_os="solana")]
#[global_allocator]
static ALLOC:solana_program::entrypoint::BumpAllocator=solana_program::entrypoint::BumpAllocator{
    start:solana_program::entrypoint::HEAP_START_ADDRESS as usize,len:256*1024};
fn hash(parts:&[&[u8]])->[u8;32]{solana_program::hash::hashv(parts).to_bytes()}
fn entry(program:&Pubkey,accounts:&[AccountInfo],_data:&[u8])->ProgramResult{
    let a=accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    if a.owner!=program || a.is_writable {return Err(ProgramError::InvalidAccountData);}
    let bytes=a.try_borrow_data()?;
    if !r101_merkle::parse_and_verify(hash,&bytes){return Err(ProgramError::Custom(101));}
    Ok(())
}
