//! Native Solana entrypoint and exact Pool V1 account composition.
//!
//! The entrypoint deliberately has no `declare_id!`: the runtime-supplied
//! `program_id` is the sole PDA domain.  A release must pin that id outside
//! this crate before any client or deployment is considered compatible.

extern crate alloc;

#[cfg(target_os = "solana")]
use alloc::format;
use alloc::{vec, vec::Vec};
use aspis_statement::pool_v1::POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES;
#[cfg(target_os = "solana")]
use solana_program::instruction::get_stack_height;
#[cfg(any(target_os = "solana", test))]
use solana_program::instruction::TRANSACTION_LEVEL_STACK_HEIGHT;
#[allow(deprecated)]
use solana_program::system_instruction;
use solana_program::{
    account_info::AccountInfo,
    clock::Clock,
    entrypoint::ProgramResult,
    instruction::{AccountMeta, Instruction},
    program,
    program_error::ProgramError,
    pubkey::Pubkey,
    rent::Rent,
    sysvar::Sysvar,
};
use solana_sdk_ids::{
    bpf_loader, bpf_loader_upgradeable, loader_v4, native_loader, system_program,
};

use crate::{
    error::PoolV1ProgramError,
    nullifier::NullifierMarkerPreparationV1,
    vault::{parse_legacy_token_account_v1, pool_v1_vault_authority_address,
        pool_v1_vault_token_account_address, LEGACY_SPL_TOKEN_ACCOUNT_BYTES,
        LEGACY_SPL_TOKEN_PROGRAM_ID, POOL_V1_VAULT_TOKEN_ACCOUNT_SEED},
};

#[cfg(feature = "pair-afterstate-evidence")]
use crate::{
    pair_dispatch::dispatch_pair_verified_afterstate_readonly_v1,
    pair_processor::{
        process_pair_private_transfer_with_verifier_v1, process_pair_withdrawal_with_verifier_v1,
    },
};

#[cfg(feature = "pair-forest-account-evidence")]
use crate::pair_forest::{
    process_pair_forest_checkpoint_with_runtime_v1, process_pair_forest_deposit_with_runtime_v1,
    process_pair_forest_initialize_with_runtime_v1, process_pair_forest_terminal_v1,
};

#[cfg(feature = "pair-forest-full-asf8-audit")]
use crate::pair_forest::process_pair_forest_terminal_full_asf8_v1;

const SPL_TOKEN_INITIALIZE_ACCOUNT3_DISCRIMINANT: u8 = 18;

#[cfg(not(feature = "no-entrypoint"))]
solana_program::entrypoint!(process_instruction);

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

}

struct SolanaPoolCpiRuntimeV1;

impl PoolCpiRuntimeV1 for SolanaPoolCpiRuntimeV1 {
    fn invoke<'info>(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'info>],
    ) -> ProgramResult {
        program::invoke(instruction, account_infos)
    }

    fn invoke_signed<'info>(
        &mut self,
        instruction: &Instruction,
        account_infos: &[AccountInfo<'info>],
        signer_seeds: &[&[&[u8]]],
    ) -> ProgramResult {
        program::invoke_signed(instruction, account_infos, signer_seeds)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FreshPdaPreparationV1 {
    CreateOrAllocateSystemOwned,
    ProgramOwnedZeroed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum VaultPreparationV1 {
    CreateAndInitialize,
    InitializedEmpty,
}

fn solana_sha256(inputs: &[&[u8]]) -> [u8; 32] {
    solana_program::hash::hashv(inputs).to_bytes()
}

fn supported_program_loader(owner: &Pubkey) -> bool {
    owner == &bpf_loader::id()
        || owner == &bpf_loader_upgradeable::id()
        || owner == &loader_v4::id()
}

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

pub(crate) fn create_or_allocate_pda<'info, R: PoolCpiRuntimeV1>(
    runtime: &mut R,
    payer: &AccountInfo<'info>,
    account: &AccountInfo<'info>,
    system_program_account: &AccountInfo<'info>,
    exact_bytes: usize,
    owner: &Pubkey,
    signer_seeds: &[&[u8]],
) -> ProgramResult {
    let rent = Rent::get()?;
    create_or_allocate_pda_with_rent(
        runtime,
        payer,
        account,
        system_program_account,
        exact_bytes,
        owner,
        signer_seeds,
        &rent,
    )
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

/// `create_with_seed` counterpart of [`create_or_allocate_pda_with_rent`]
/// (B1 marker). `base` is a Pool PDA that signs with `base_signer_seeds`;
/// `account` must be `create_with_seed(base, seed, owner)` (the System
/// program re-derives and checks it). A System-owned empty account with no
/// lamports is created with `CreateAccountWithSeed`; a prefunded one (anyone
/// may send lamports to the address first) is topped up with `Transfer` and
/// then given its space and owner with `AllocateWithSeed` and
/// `AssignWithSeed`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn create_or_allocate_with_seed_with_rent<'info, R: PoolCpiRuntimeV1>(
    runtime: &mut R,
    payer: &AccountInfo<'info>,
    account: &AccountInfo<'info>,
    base: &AccountInfo<'info>,
    seed: &str,
    system_program_account: &AccountInfo<'info>,
    exact_bytes: usize,
    owner: &Pubkey,
    base_signer_seeds: &[&[u8]],
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
        base.clone(),
        system_program_account.clone(),
    ];
    let signer_seed_sets = [base_signer_seeds];
    if account.lamports() == 0 {
        runtime.invoke_signed(
            &system_instruction::create_account_with_seed(
                payer.key,
                account.key,
                base.key,
                seed,
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
            &system_instruction::allocate_with_seed(
                account.key,
                base.key,
                seed,
                exact_bytes as u64,
                owner,
            ),
            &infos,
            &signer_seed_sets,
        )?;
        runtime.invoke_signed(
            &system_instruction::assign_with_seed(account.key, base.key, seed, owner),
            &infos,
            &signer_seed_sets,
        )?;
    }
    Ok(())
}

pub(crate) fn require_token_program_account(account: &AccountInfo<'_>) -> ProgramResult {
    if account.key != &LEGACY_SPL_TOKEN_PROGRAM_ID
        || !account.executable
        || account.is_signer
        || account.is_writable
        || !supported_program_loader(account.owner)
    {
        return Err(PoolV1ProgramError::InvalidTokenProgram.into());
    }
    Ok(())
}

fn require_initialized_empty_vault(
    program_id: &Pubkey,
    pool: &Pubkey,
    mint: &Pubkey,
    vault: &AccountInfo<'_>,
) -> ProgramResult {
    if vault.key != &pool_v1_vault_token_account_address(program_id, pool).0
        || vault.owner != &LEGACY_SPL_TOKEN_PROGRAM_ID
        || vault.executable
        || vault.is_signer
        || !vault.is_writable
    {
        return Err(PoolV1ProgramError::InvalidVaultTokenAddress.into());
    }
    let parsed = parse_legacy_token_account_v1(&vault.try_borrow_data()?)?;
    if parsed.mint != *mint
        || parsed.authority != pool_v1_vault_authority_address(program_id, pool).0
        || parsed.amount != 0
        || parsed.has_delegate
        || parsed.is_native
        || parsed.delegated_amount != 0
        || parsed.has_close_authority
    {
        return Err(PoolV1ProgramError::UnsupportedTokenConfiguration.into());
    }
    Ok(())
}

pub(crate) fn plan_vault_initialization(
    program_id: &Pubkey,
    pool: &Pubkey,
    mint: &Pubkey,
    vault: &AccountInfo<'_>,
) -> Result<VaultPreparationV1, ProgramError> {
    if vault.key != &pool_v1_vault_token_account_address(program_id, pool).0
        || vault.executable
        || vault.is_signer
        || !vault.is_writable
    {
        return Err(PoolV1ProgramError::InvalidVaultTokenAddress.into());
    }
    if vault.owner == &system_program::id() && vault.data_is_empty() {
        Ok(VaultPreparationV1::CreateAndInitialize)
    } else {
        require_initialized_empty_vault(program_id, pool, mint, vault)?;
        Ok(VaultPreparationV1::InitializedEmpty)
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn initialize_vault_account<'info, R: PoolCpiRuntimeV1>(
    runtime: &mut R,
    program_id: &Pubkey,
    pool: &Pubkey,
    mint: &AccountInfo<'info>,
    vault: &AccountInfo<'info>,
    token_program: &AccountInfo<'info>,
    payer: &AccountInfo<'info>,
    system_program_account: &AccountInfo<'info>,
    preparation: VaultPreparationV1,
) -> ProgramResult {
    if preparation == VaultPreparationV1::InitializedEmpty {
        return Ok(());
    }
    let (_, bump) = pool_v1_vault_token_account_address(program_id, pool);
    let bump_seed = [bump];
    let seeds: &[&[u8]] = &[POOL_V1_VAULT_TOKEN_ACCOUNT_SEED, pool.as_ref(), &bump_seed];
    create_or_allocate_pda(
        runtime,
        payer,
        vault,
        system_program_account,
        LEGACY_SPL_TOKEN_ACCOUNT_BYTES,
        &LEGACY_SPL_TOKEN_PROGRAM_ID,
        seeds,
    )?;

    let authority = pool_v1_vault_authority_address(program_id, pool).0;
    let mut data = Vec::with_capacity(33);
    data.push(SPL_TOKEN_INITIALIZE_ACCOUNT3_DISCRIMINANT);
    data.extend_from_slice(authority.as_ref());
    let instruction = Instruction {
        program_id: LEGACY_SPL_TOKEN_PROGRAM_ID,
        accounts: vec![
            AccountMeta::new(*vault.key, false),
            AccountMeta::new_readonly(*mint.key, false),
        ],
        data,
    };
    runtime.invoke(
        &instruction,
        &[vault.clone(), mint.clone(), token_program.clone()],
    )?;
    require_initialized_empty_vault(program_id, pool, mint.key, vault)
}

/// Create the pair-forest (B1) marker at `create_with_seed(master, seed,
/// program_id)` if it is still System-owned, signing as the master PDA
/// (`master_signer_seeds` = master seeds with the stored, authenticated
/// bump). The key was authenticated by the plan, so the re-check derives no
/// address: it only requires the now Pool-owned, exact-size, zeroed,
/// rent-exempt image.
#[allow(clippy::too_many_arguments)]
#[cfg(feature = "pair-forest-account-evidence")]
pub(crate) fn create_pair_forest_nullifier_marker_if_needed_v1<'info, R: PoolCpiRuntimeV1>(
    runtime: &mut R,
    program_id: &Pubkey,
    master_account: &AccountInfo<'info>,
    master_signer_seeds: &[&[u8]],
    marker_account: &AccountInfo<'info>,
    payer: &AccountInfo<'info>,
    system_program_account: &AccountInfo<'info>,
    planned: crate::nullifier::PlannedPairForestNullifierMarkerV1,
    rent: &Rent,
) -> Result<crate::nullifier::PlannedPairForestNullifierMarkerV1, ProgramError> {
    if planned.preparation() == NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned {
        create_or_allocate_with_seed_with_rent(
            runtime,
            payer,
            marker_account,
            master_account,
            crate::nullifier::pool_v1_pair_forest_marker_seed_str_v1(planned.seed())?,
            system_program_account,
            POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES,
            program_id,
            master_signer_seeds,
            rent,
        )?;
    }
    if crate::nullifier::recheck_pair_forest_nullifier_marker_v1(program_id, marker_account)?
        != NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed
        || !rent.is_exempt(
            marker_account.lamports(),
            POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES,
        )
    {
        return Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into());
    }
    Ok(planned)
}

/// Exact native Pool dispatcher. Return data is cleared at entry and again on
/// every error, so an accepted verifier's intermediate `ASVS` cannot escape a
/// later failed marker/tree/vault transition.
#[inline(never)]
pub fn process_instruction(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    program::set_return_data(&[]);
    // The finalized wallet/indexer authenticates transaction-level Pool
    // instructions.  Rejecting CPI here prevents an inner invocation from
    // advancing the append-only tree without a corresponding top-level scan
    // record.  Host unit tests exercise the pure predicate below; LiteSVM and
    // validator release gates exercise the production syscall.
    #[cfg(target_os = "solana")]
    require_transaction_level_invocation_v1(get_stack_height())?;
    let magic = instruction_data
        .get(..4)
        .ok_or(ProgramError::InvalidInstructionData)?;
    let mut runtime = SolanaPoolCpiRuntimeV1;
    let result = if cfg!(feature = "pair-forest-account-evidence") && magic == b"AS8I" {
        #[cfg(feature = "pair-forest-account-evidence")]
        {
            let rent = Rent::get()?;
            process_pair_forest_initialize_with_runtime_v1(
                program_id,
                accounts,
                instruction_data,
                &rent,
                &mut runtime,
            )
        }
        #[cfg(not(feature = "pair-forest-account-evidence"))]
        unreachable!()
    } else if cfg!(feature = "pair-forest-account-evidence") && magic == b"AS8C" {
        #[cfg(feature = "pair-forest-account-evidence")]
        {
            let rent = Rent::get()?;
            process_pair_forest_checkpoint_with_runtime_v1(
                program_id,
                accounts,
                instruction_data,
                &rent,
                &mut runtime,
            )
        }
        #[cfg(not(feature = "pair-forest-account-evidence"))]
        unreachable!()
    } else if cfg!(feature = "pair-forest-account-evidence") && magic == b"AS8D" {
        #[cfg(feature = "pair-forest-account-evidence")]
        {
            let rent = Rent::get()?;
            process_pair_forest_deposit_with_runtime_v1(
                program_id,
                accounts,
                instruction_data,
                &rent,
                &mut runtime,
            )
        }
        #[cfg(not(feature = "pair-forest-account-evidence"))]
        unreachable!()
    } else if cfg!(feature = "pair-forest-account-evidence") && magic == b"ASQ8" {
        #[cfg(feature = "pair-forest-account-evidence")]
        {
            let slot = Clock::get()?.slot;
            let rent = Rent::get()?;
            process_pair_forest_terminal_v1(
                program_id,
                accounts,
                instruction_data,
                slot,
                &rent,
                &mut runtime,
            )
        }
        #[cfg(not(feature = "pair-forest-account-evidence"))]
        unreachable!()
    } else if cfg!(feature = "pair-forest-full-asf8-audit") && magic == b"ASF8" {
        #[cfg(feature = "pair-forest-full-asf8-audit")]
        {
            let slot = Clock::get()?.slot;
            let rent = Rent::get()?;
            process_pair_forest_terminal_full_asf8_v1(
                program_id,
                accounts,
                instruction_data,
                slot,
                &rent,
                &mut runtime,
            )
        }
        #[cfg(not(feature = "pair-forest-full-asf8-audit"))]
        unreachable!()
    } else if cfg!(feature = "pair-afterstate-evidence")
        && magic == crate::instruction::POOL_V1_PAIR_PRIVATE_TRANSFER_INSTRUCTION_MAGIC
    {
        #[cfg(feature = "pair-afterstate-evidence")]
        {
            let slot = Clock::get()?.slot;
            process_pair_private_transfer_with_verifier_v1(
                program_id,
                accounts,
                instruction_data,
                slot,
                solana_sha256,
                dispatch_pair_verified_afterstate_readonly_v1,
                program::set_return_data,
            )
        }
        #[cfg(not(feature = "pair-afterstate-evidence"))]
        unreachable!()
    } else if cfg!(feature = "pair-afterstate-evidence")
        && magic == crate::instruction::POOL_V1_PAIR_WITHDRAWAL_INSTRUCTION_MAGIC
    {
        #[cfg(feature = "pair-afterstate-evidence")]
        {
            let slot = Clock::get()?.slot;
            process_pair_withdrawal_with_verifier_v1(
                program_id,
                accounts,
                instruction_data,
                slot,
                solana_sha256,
                &mut runtime,
                dispatch_pair_verified_afterstate_readonly_v1,
                program::set_return_data,
            )
        }
        #[cfg(not(feature = "pair-afterstate-evidence"))]
        unreachable!()
    } else {
        Err(ProgramError::InvalidInstructionData)
    };
    if result.is_err() {
        program::set_return_data(&[]);
    }
    result
}

#[cfg(any(target_os = "solana", test))]
#[inline(always)]
fn require_transaction_level_invocation_v1(stack_height: usize) -> ProgramResult {
    if stack_height != TRANSACTION_LEVEL_STACK_HEIGHT {
        return Err(PoolV1ProgramError::CpiInvocationForbidden.into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
fn public_dispatch_rejects_short_and_unknown_instruction_headers() {
        let program_id = Pubkey::new_unique();
        assert_eq!(
            process_instruction(&program_id, &[], b"ASP"),
            Err(ProgramError::InvalidInstructionData)
        );
        assert_eq!(
            process_instruction(&program_id, &[], b"NOPE"),
            Err(ProgramError::InvalidInstructionData)
        );
    }
    #[test]
fn transaction_level_gate_rejects_every_cpi_stack_height() {
        assert_eq!(
            require_transaction_level_invocation_v1(TRANSACTION_LEVEL_STACK_HEIGHT),
            Ok(())
        );
        for stack_height in [
            0,
            TRANSACTION_LEVEL_STACK_HEIGHT + 1,
            TRANSACTION_LEVEL_STACK_HEIGHT + 2,
            usize::MAX,
        ] {
            assert_eq!(
                require_transaction_level_invocation_v1(stack_height),
                Err(PoolV1ProgramError::CpiInvocationForbidden.into())
            );
        }
    }
    #[test]
    fn removed_legacy_instruction_magics_are_rejected() {
        let program_id = Pubkey::new_unique();
        for magic in [b"ASIN", b"ASDI", b"ASPT", b"ASWD", b"ASPP", b"ASPF", b"ASPX"] {
            for length in [4usize, 184, 512, 1880] {
                let mut bytes = std::vec![0u8; length];
                bytes[..4].copy_from_slice(magic);
                assert_eq!(process_instruction(&program_id, &[], &bytes),
                    Err(ProgramError::InvalidInstructionData), "{:?}, length {}", magic, length);
            }
        }
    }

}

#[cfg(kani)]
#[path="PCG_368.rs"]
mod PCG_368;
