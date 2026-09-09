//! Unchanged selected registry processor, matched research build wrapper.
#![allow(unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,pubkey::Pubkey};
solana_program::entrypoint!(entry);
#[cfg(target_os="solana")]
#[global_allocator]
static ALLOC:solana_program::entrypoint::BumpAllocator=solana_program::entrypoint::BumpAllocator{
    start:solana_program::entrypoint::HEAP_START_ADDRESS as usize,len:256*1024};
fn entry(id:&Pubkey,accounts:&[AccountInfo],instruction:&[u8])->ProgramResult{
    aspis_registry::process_instruction(id,accounts,instruction)
}
