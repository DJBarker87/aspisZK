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
// Diagnostic-only cross-crate checkpoints; absent from the quiet winning ELF.
#[cfg(v8_terminal_profile)]
#[no_mangle]
pub extern "C" fn aspis_v8_terminal_checkpoint(tag:u64) {
    match tag {
        1 => solana_program::msg!("v8:terminal-selectors"),
        2 => solana_program::msg!("v8:terminal-poseidon"),
        3 => solana_program::msg!("v8:terminal-semantic"),
        4 => solana_program::msg!("v8:terminal-copy"),
        5 => solana_program::msg!("v8:terminal-blend"),
        _ => panic!("invalid research profile tag"),
    }
    solana_program::log::sol_log_compute_units();
}
