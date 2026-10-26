//! Proof-only isolated source slices. No shipped-source changes.
use solana_program::{account_info::AccountInfo, pubkey::Pubkey, program_error::ProgramError,
    entrypoint::ProgramResult, rent::Rent, system_program};
mod error;
use error::PoolV1ProgramError;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum FreshPdaPreparationV1 { CreateOrAllocateSystemOwned, ProgramOwnedZeroed }


pub(crate) fn require_program_account(
    account: &AccountInfo,
    program_id: &Pubkey,
    writable: bool,
) -> Result<(), ProgramError> {
    if account.owner != program_id {
        return Err(ProgramError::IncorrectProgramId);
    }
    if account.executable || account.is_writable != writable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

fn require_program_owned_zeroed(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    exact_bytes: usize,
    rent: &Rent,
) -> ProgramResult {
    require_program_account(account, program_id, true)?;
    let data = account.try_borrow_data()?;
    if data.len() != exact_bytes
        || data.iter().any(|byte| *byte != 0)
        || !rent.is_exempt(account.lamports(), exact_bytes)
    {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    Ok(())
}

pub(crate) fn plan_fresh_program_pda(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    expected_address: &Pubkey,
    exact_bytes: usize,
) -> Result<FreshPdaPreparationV1, ProgramError> {
    if account.key != expected_address
        || account.executable
        || account.is_signer
        || !account.is_writable
    {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    if account.owner == program_id {
        let data = account.try_borrow_data()?;
        if data.len() != exact_bytes || data.iter().any(|byte| *byte != 0) {
            return Err(PoolV1ProgramError::InvalidFreshAccount.into());
        }
        Ok(FreshPdaPreparationV1::ProgramOwnedZeroed)
    } else if account.owner == &system_program::id() && account.data_is_empty() {
        Ok(FreshPdaPreparationV1::CreateOrAllocateSystemOwned)
    } else {
        Err(PoolV1ProgramError::InvalidFreshAccount.into())
    }
}

struct PoolW_Planned { checkpoint_image: [u8;192], next_master_image: [u8;384] }
fn PoolW_copy_tail(master: &AccountInfo<'_>, checkpoint: &AccountInfo<'_>, planned: &PoolW_Planned) -> ProgramResult {
    let mut master_data = master.try_borrow_mut_data()?;
    let mut checkpoint_data = checkpoint.try_borrow_mut_data()?;
    checkpoint_data.copy_from_slice(&planned.checkpoint_image);
    master_data.copy_from_slice(&planned.next_master_image);
    Ok(())
}

#[cfg(kani)]
include!("PoolW_harness.rs");
