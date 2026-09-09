//! Isolated experimental COMPLETE verifier plus existing proof lifecycle.
#![allow(unexpected_cfgs)]
use solana_program::{account_info::AccountInfo, entrypoint::ProgramResult, pubkey::Pubkey};
solana_program::entrypoint!(entry);
#[cfg(target_os = "solana")]
#[global_allocator]
static ALLOC: solana_program::entrypoint::BumpAllocator = solana_program::entrypoint::BumpAllocator {
    start: solana_program::entrypoint::HEAP_START_ADDRESS as usize, len: 256 * 1024,
};
fn entry(id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    if data.starts_with(b"ASQ8") {
        aspis_verifier::v7_pair_forest_dispatch::process_v7_pair_forest_asq8_instruction(id, accounts, data)
    } else {
        aspis_verifier::v8_devnet_lifecycle::process(id, accounts, data)
    }
}
