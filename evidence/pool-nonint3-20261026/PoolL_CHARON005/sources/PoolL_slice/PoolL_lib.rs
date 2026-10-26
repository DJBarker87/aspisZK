use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError,entrypoint::ProgramResult,system_program};
use solana_sdk_ids::native_loader;
mod error;
use error::PoolV1ProgramError;
pub fn require_payer_and_system_program(
    payer: &AccountInfo<'_>,
    system_program_account: &AccountInfo<'_>,
) -> ProgramResult {
    if !payer.is_signer
        || !payer.is_writable
        || payer.executable
        || payer.owner != &system_program::id()
    {
        return Err(PoolV1ProgramError::InvalidPayer.into());
    }
    if system_program_account.key != &system_program::id()
        || system_program_account.owner != &native_loader::id()
        || !system_program_account.executable
        || system_program_account.is_signer
        || system_program_account.is_writable
    {
        return Err(PoolV1ProgramError::InvalidSystemProgram.into());
    }
    Ok(())
}
pub fn PoolL_close_prefix(
    account: &AccountInfo<'_>,
    refund_authority: &AccountInfo<'_>,
    expected_owner: &Pubkey,
    expected_data_len: usize,
) -> ProgramResult {
    if account.owner != expected_owner
        || account.executable
        || account.is_signer
        || !account.is_writable
        || refund_authority.key == account.key
        || !refund_authority.is_writable
        || account.data_len() != expected_data_len
    {
        return Err(ProgramError::InvalidAccountData);
    }

    Ok(())
}

#[derive(Clone,Copy,PartialEq,Eq)]
pub enum FreshPdaPreparationV1 { CreateOrAllocateSystemOwned, ProgramOwnedZeroed }
pub fn plan_fresh_program_pda(
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

// Length-first source cut: first disjunct of state.rs decode guards.
// The remaining header disjuncts and decoder form an unexecuted suffix on mismatch.
pub fn PoolL_length_prefix(data: &[u8], expected: usize) -> ProgramResult {
    if data.len() != expected {
        return Err(PoolV1ProgramError::InvalidAccountType.into());
    }
    Ok(())
}
