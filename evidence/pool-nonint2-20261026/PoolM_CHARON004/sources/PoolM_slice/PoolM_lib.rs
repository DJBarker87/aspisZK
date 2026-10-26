use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError,entrypoint::ProgramResult,system_program};
mod error;
use error::PoolV1ProgramError;
mod instruction { pub const POOL_V1_INSTRUCTION_VERSION:u8=1; }
mod cancel_prepared_settlement_instruction;
use cancel_prepared_settlement_instruction::*;
const POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES:usize=10000;
const POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES:usize=8504;
pub(crate) fn require_unique_accounts(accounts: &[AccountInfo<'_>]) -> ProgramResult {
    for left in 0..accounts.len() {
        for right in left + 1..accounts.len() {
            if accounts[left].key == accounts[right].key {
                return Err(ProgramError::InvalidArgument);
            }
        }
    }
    Ok(())
}
fn require_prepared_plan_account_v1(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    exact_data_len: usize,
) -> ProgramResult {
    if account.owner != program_id
        || account.executable
        || account.is_signer
        || !account.is_writable
        || account.data_len() != exact_data_len
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
pub fn PoolM_cancel_prefix(program_id:&Pubkey,accounts:&[AccountInfo<'_>],instruction_data:&[u8])->ProgramResult {
    let instruction = decode_cancel_prepared_settlement_instruction_v1(instruction_data)?;
    let expected_accounts = instruction.account_shape.account_count();
    if accounts.len() != expected_accounts {
        return Err(if accounts.len() < expected_accounts {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    require_unique_accounts(accounts)?;

    let plan_authority = &accounts[0];
    if !plan_authority.is_signer
        || !plan_authority.is_writable
        || plan_authority.executable
        || plan_authority.owner != &system_program::id()
    {
        return Err(PoolV1ProgramError::InvalidPayer.into());
    }
    let core_plan = &accounts[1];
    require_prepared_plan_account_v1(
        core_plan,
        program_id,
        POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES,
    )?;
    let rollover_plan = instruction
        .account_shape
        .has_rollover_shard()
        .then(|| &accounts[2]);
    if let Some(shard) = rollover_plan {
        require_prepared_plan_account_v1(
            shard,
            program_id,
            POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES,
        )?;
    }

    Ok(())
}

// Split source cut after parser/count/unique and account role selection.
pub fn PoolM_cancel_roles_native(program_id:&Pubkey,plan_authority:&AccountInfo<'_>,core_plan:&AccountInfo<'_>,shard:&AccountInfo<'_>,has_shard:bool)->ProgramResult {
    if !plan_authority.is_signer
        || !plan_authority.is_writable
        || plan_authority.executable
        || plan_authority.owner != &system_program::id()
    {
        return Err(PoolV1ProgramError::InvalidPayer.into());
    }
    require_prepared_plan_account_v1(core_plan,program_id,POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES)?;
    if has_shard {
        require_prepared_plan_account_v1(shard,program_id,POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES)?;
    }
    Ok(())
}
