//! Local SVM benchmark ONLY. Read-only proof/public accounts. No pool writes.
#![allow(unexpected_cfgs,dead_code)]
use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,program_error::ProgramError,pubkey::Pubkey};
#[path="../relation_callback.rs"]
mod callback;
solana_program::entrypoint!(entry);
#[cfg(target_os="solana")]
#[global_allocator]
static ALLOC:solana_program::entrypoint::BumpAllocator=solana_program::entrypoint::BumpAllocator{
    start:solana_program::entrypoint::HEAP_START_ADDRESS as usize,len:256*1024};
fn entry(_id:&Pubkey,accounts:&[AccountInfo],instruction:&[u8])->ProgramResult{
    if accounts.len()!=3||instruction.len()!=32||accounts.iter().any(|a|a.is_writable){return Err(ProgramError::InvalidArgument);}
    let body=accounts[0].try_borrow_data()?;
    let public=accounts[1].try_borrow_data()?;
    let transition=accounts[2].try_borrow_data()?;
    callback::performance_verifier::verify(&body,instruction.try_into().unwrap(),&public,&transition).map_err(ProgramError::Custom)
}
