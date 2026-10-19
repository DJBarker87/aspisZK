#![allow(dead_code)]
// Namespace-only wrapper. These are the exact SDK types reexported by solana_program.
pub mod r1_pool_adapter {
use solana_account_info::AccountInfo;
use solana_pubkey::Pubkey;
use solana_program_error::{ProgramError, ProgramResult};

fn require_readonly_account(account: &AccountInfo<'_>, owner: &Pubkey) -> ProgramResult {
    if account.owner != owner || account.is_signer || account.is_writable || account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
}
