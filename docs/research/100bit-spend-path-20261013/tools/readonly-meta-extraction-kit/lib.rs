#![allow(dead_code)]
// Exact production helper; real SDK Pubkey/ProgramError, no AccountInfo model.
pub mod readonly_meta {
use solana_pubkey::Pubkey;
use solana_program_error::{ProgramError, ProgramResult};

fn readonly_meta_ok(
    owner: &Pubkey,
    expected: &Pubkey,
    is_signer: bool,
    is_writable: bool,
    executable: bool,
) -> ProgramResult {
    if owner != expected || is_signer || is_writable || executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
}
