//! Byte-identical native System-CPI construction and ordering slice.
use solana_program::{account_info::AccountInfo, pubkey::Pubkey, program_error::ProgramError,
 entrypoint::ProgramResult, rent::Rent, system_program, system_instruction, instruction::Instruction};
use solana_sdk_ids::native_loader;
mod error;use error::PoolV1ProgramError;

pub(crate) trait PoolCpiRuntimeV1 {
    fn invoke<'info>(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'info>],
    ) -> ProgramResult;

    fn invoke_signed<'info>(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'info>],
        signer_seeds: &[&[&[u8]]],
    ) -> ProgramResult;

    fn close_program_account<'info>(
        &mut self,
        account: &AccountInfo<'info>,
        refund_authority: &AccountInfo<'info>,
        expected_owner: &Pubkey,
        expected_data_len: usize,
    ) -> ProgramResult {
        close_program_account_v1(account, refund_authority, expected_owner, expected_data_len)
    }
}

pub(crate) fn require_payer_and_system_program(
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

fn close_program_account_v1(
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

    // A full tombstone precedes the zero-lamport state. If a later operation
    // in this instruction fails, transaction rollback restores the plan; if
    // settlement succeeds, resize+System assignment prevent same-transaction
    // account revival from restoring a decodable ASPS/ASRS image.
    account.try_borrow_mut_data()?.fill(0xff);
    let refund = account.lamports();
    {
        let mut destination_lamports = refund_authority.try_borrow_mut_lamports()?;
        let mut account_lamports = account.try_borrow_mut_lamports()?;
        let next = (**destination_lamports)
            .checked_add(refund)
            .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
        **destination_lamports = next;
        **account_lamports = 0;
    }
    account.assign(&system_program::id());
    account.resize(0)?;
    Ok(())
}

pub(crate) fn create_or_allocate_pda_with_rent<'info, R: PoolCpiRuntimeV1>(
    runtime: &mut R,
    payer: &AccountInfo<'info>,
    account: &AccountInfo<'info>,
    system_program_account: &AccountInfo<'info>,
    exact_bytes: usize,
    owner: &Pubkey,
    signer_seeds: &[&[u8]],
    rent: &Rent,
) -> ProgramResult {
    require_payer_and_system_program(payer, system_program_account)?;
    if account.owner != &system_program::id() || !account.data_is_empty() {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    let required_lamports = rent.minimum_balance(exact_bytes).max(1);
    let infos = [
        payer.clone(),
        account.clone(),
        system_program_account.clone(),
    ];
    let signer_seed_sets = [signer_seeds];
    if account.lamports() == 0 {
        runtime.invoke_signed(
            &system_instruction::create_account(
                payer.key,
                account.key,
                required_lamports,
                exact_bytes as u64,
                owner,
            ),
            &infos,
            &signer_seed_sets,
        )?;
    } else {
        let deficit = required_lamports.saturating_sub(account.lamports());
        if deficit != 0 {
            runtime.invoke(
                &system_instruction::transfer(payer.key, account.key, deficit),
                &infos,
            )?;
        }
        runtime.invoke_signed(
            &system_instruction::allocate(account.key, exact_bytes as u64),
            &infos,
            &signer_seed_sets,
        )?;
        runtime.invoke_signed(
            &system_instruction::assign(account.key, owner),
            &infos,
            &signer_seed_sets,
        )?;
    }
    Ok(())
}

#[cfg(kani)]
include!("PoolV_harness.rs");
