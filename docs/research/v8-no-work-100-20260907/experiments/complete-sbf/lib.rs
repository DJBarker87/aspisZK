//! Research-only complete authenticated ASQ8 verifier; no production dispatcher.
#![allow(unexpected_cfgs)]
use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,pubkey::Pubkey};
solana_program::entrypoint!(entry);
#[cfg(target_os="solana")]
#[global_allocator]
static ALLOC:solana_program::entrypoint::BumpAllocator=solana_program::entrypoint::BumpAllocator{
    start:solana_program::entrypoint::HEAP_START_ADDRESS as usize,len:256*1024};
fn entry(id:&Pubkey,accounts:&[AccountInfo],instruction:&[u8])->ProgramResult{
    aspis_verifier::v7_pair_forest_dispatch::process_v7_pair_forest_asq8_instruction(id,accounts,instruction)
}
