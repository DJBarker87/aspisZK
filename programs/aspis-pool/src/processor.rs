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

/// The key of `accounts[index]`, or the zero key past the end. A conditional write into a key array in a function
/// that holds AccountInfo values is rejected by the translator (nested borrows at the join); this helper returns a
/// plain value instead.
pub(crate) fn account_key_or_zero(accounts: &[AccountInfo<'_>], index: usize) -> Pubkey {
    if index < accounts.len() {
        *accounts[index].key
    } else {
        Pubkey::new_from_array([0u8; 32])
    }
}

/// Largest account list `require_unique_accounts` accepts. Every caller first requires an exact account count no
/// larger than this (terminal at most 18, initialize 14, checkpoint 12, deposit at most 11).
pub(crate) const UNIQUE_ACCOUNTS_MAX: usize = 18;

/// Pairwise scan over plain keys, in the order of the former nested loop (left ascending, then right ascending);
/// stops at the first repeated pair.
pub(crate) fn keys_repeat(keys: &[Pubkey; UNIQUE_ACCOUNTS_MAX], count: usize) -> bool {
    // One loop over the (left, right) pairs; a nested loop is rejected by the translator (nested borrows in the
    // loop join).
    let mut repeat = false;
    let mut left = 0;
    let mut right = 1;
    while !repeat && left < count {
        if right < count {
            repeat = keys[left] == keys[right];
            right += 1;
        } else {
            left += 1;
            right = left + 1;
        }
    }
    repeat
}

pub(crate) fn require_unique_accounts(accounts: &[AccountInfo<'_>]) -> ProgramResult {
    // The translator rejects any loop in a function that holds an
    // AccountInfo, so the keys are copied, written out without a loop, through `account_key_or_zero` into a plain array, and the
    // pairwise scan runs in a helper that sees only that array. A list longer than UNIQUE_ACCOUNTS_MAX is rejected
    // with the duplicate error; no caller can pass one (each requires an exact count of at most 18 first).
    let count = accounts.len();
    if count > UNIQUE_ACCOUNTS_MAX {
        return Err(ProgramError::InvalidArgument);
    }
    let keys: [Pubkey; UNIQUE_ACCOUNTS_MAX] = [
        account_key_or_zero(accounts, 0),
        account_key_or_zero(accounts, 1),
        account_key_or_zero(accounts, 2),
        account_key_or_zero(accounts, 3),
        account_key_or_zero(accounts, 4),
        account_key_or_zero(accounts, 5),
        account_key_or_zero(accounts, 6),
        account_key_or_zero(accounts, 7),
        account_key_or_zero(accounts, 8),
        account_key_or_zero(accounts, 9),
        account_key_or_zero(accounts, 10),
        account_key_or_zero(accounts, 11),
        account_key_or_zero(accounts, 12),
        account_key_or_zero(accounts, 13),
        account_key_or_zero(accounts, 14),
        account_key_or_zero(accounts, 15),
        account_key_or_zero(accounts, 16),
        account_key_or_zero(accounts, 17),
    ];
    if keys_repeat(&keys, count) {
        return Err(ProgramError::InvalidArgument);
    }
    Ok(())
}

#[cfg(test)]
mod x2b_unique_accounts_differential {
    use super::*;

    /// The frozen body of `require_unique_accounts` (commit 3d700effcabe), kept for comparison.
    fn frozen_require_unique_accounts(accounts: &[AccountInfo<'_>]) -> ProgramResult {
        for left in 0..accounts.len() {
            for right in left + 1..accounts.len() {
                if accounts[left].key == accounts[right].key {
                    return Err(ProgramError::InvalidArgument);
                }
            }
        }
        Ok(())
    }

    fn next(state: &mut u64) -> u64 {
        *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        *state >> 33
    }

    fn check(keys: &[Pubkey]) {
        let owner = Pubkey::new_from_array([9u8; 32]);
        let mut lamports = [0u64; UNIQUE_ACCOUNTS_MAX];
        let mut data = [[0u8; 1]; UNIQUE_ACCOUNTS_MAX];
        let mut infos = alloc::vec::Vec::new();
        for ((key, lamport), datum) in keys.iter().zip(lamports.iter_mut()).zip(data.iter_mut()) {
            infos.push(AccountInfo::new(key, false, false, lamport, datum, &owner, false, 0));
        }
        assert_eq!(require_unique_accounts(&infos), frozen_require_unique_accounts(&infos), "{keys:?}");
    }

    #[test]
    fn same_result_as_frozen_loop() {
        let mut state = 0x5eed_u64;
        for count in 0..=UNIQUE_ACCOUNTS_MAX {
            // all distinct
            let distinct: alloc::vec::Vec<Pubkey> =
                (0..count).map(|i| Pubkey::new_from_array([i as u8 + 1; 32])).collect();
            check(&distinct);
            // every single duplicated pair, including first/last positions
            for left in 0..count {
                for right in left + 1..count {
                    let mut keys = distinct.clone();
                    keys[right] = keys[left];
                    check(&keys);
                }
            }
            // random keys from a small alphabet (frequent repeats) and from a large one
            for _ in 0..200 {
                let small: alloc::vec::Vec<Pubkey> = (0..count)
                    .map(|_| Pubkey::new_from_array([(next(&mut state) % 6) as u8; 32]))
                    .collect();
                check(&small);
                let large: alloc::vec::Vec<Pubkey> = (0..count)
                    .map(|_| {
                        let mut b = [0u8; 32];
                        b[..8].copy_from_slice(&next(&mut state).to_le_bytes());
                        Pubkey::new_from_array(b)
                    })
                    .collect();
                check(&large);
            }
        }
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

pub(crate) fn plan_fresh_program_pda(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    expected_address: &Pubkey,
    exact_bytes: usize,
) -> Result<FreshPdaPreparationV1, ProgramError> {
    if *account.key != *expected_address
        || account.executable
        || account.is_signer
        || !account.is_writable
    {
        return Err(PoolV1ProgramError::InvalidFreshAccount.into());
    }
    if *account.owner == *program_id {
        let data = match account.try_borrow_data() {
            Ok(data) => data,
            Err(err) => return Err(err),
        };
        if data.len() != exact_bytes || !crate::history::page_bytes_are_zero(&data) {
            return Err(PoolV1ProgramError::InvalidFreshAccount.into());
        }
        Ok(FreshPdaPreparationV1::ProgramOwnedZeroed)
    } else if *account.owner == system_program::id() && account.data_is_empty() {
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
    if *account.owner != system_program::id() || !account.data_is_empty() {
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
    if *account.owner != system_program::id() || !account.data_is_empty() {
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
    vault_account: &AccountInfo<'_>,
) -> ProgramResult {
    if *vault_account.key != pool_v1_vault_token_account_address(program_id, pool).0
        || *vault_account.owner != LEGACY_SPL_TOKEN_PROGRAM_ID
        || vault_account.executable
        || vault_account.is_signer
        || !vault_account.is_writable
    {
        return Err(PoolV1ProgramError::InvalidVaultTokenAddress.into());
    }
    let parsed = {
        let data = match vault_account.try_borrow_data() {
            Ok(data) => data,
            Err(err) => return Err(err),
        };
        parse_legacy_token_account_v1(&data)?
    };
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
    vault_account: &AccountInfo<'_>,
) -> Result<VaultPreparationV1, ProgramError> {
    if *vault_account.key != pool_v1_vault_token_account_address(program_id, pool).0
        || vault_account.executable
        || vault_account.is_signer
        || !vault_account.is_writable
    {
        return Err(PoolV1ProgramError::InvalidVaultTokenAddress.into());
    }
    if *vault_account.owner == system_program::id() && vault_account.data_is_empty() {
        Ok(VaultPreparationV1::CreateAndInitialize)
    } else {
        require_initialized_empty_vault(program_id, pool, mint, vault_account)?;
        Ok(VaultPreparationV1::InitializedEmpty)
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn initialize_vault_account<'info, R: PoolCpiRuntimeV1>(
    runtime: &mut R,
    program_id: &Pubkey,
    pool: &Pubkey,
    mint: &AccountInfo<'info>,
    vault_account: &AccountInfo<'info>,
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
        vault_account,
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
            AccountMeta::new(*vault_account.key, false),
            AccountMeta::new_readonly(*mint.key, false),
        ],
        data,
    };
    runtime.invoke(
        &instruction,
        &[vault_account.clone(), mint.clone(), token_program.clone()],
    )?;
    require_initialized_empty_vault(program_id, pool, mint.key, vault_account)
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
    require_transaction_level_invocation_v1(runtime_stack_height_v1())?;
    // A length check and a range index instead of `get(..4).ok_or(..)?` (`ok_or` does not
    // elaborate on the native library); `get(..4)` is None exactly when the length is below 4.
    if instruction_data.len() < 4 {
        return Err(ProgramError::InvalidInstructionData);
    }
    // Translatable form (inference row): the dispatch chain is a helper. Its outer error is an early `?` exit of the frozen
    // chain (a sysvar read), returned as before without the second `set_return_data`; its inner value is the
    // handler's result. With the chain inlined, the translator propagated the final `Err` literal into `is_err` and
    // its type argument could not be inferred.
    let result = match dispatch_pool_instruction_v1(program_id, accounts, instruction_data) {
        Ok(result) => result,
        Err(err) => return Err(err),
    };
    if result.is_err() {
        program::set_return_data(&[]);
    }
    result
}

/// The frozen dispatch chain of `process_instruction`, unchanged, as a helper (see the caller).
#[inline(always)]
fn dispatch_pool_instruction_v1(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> Result<ProgramResult, ProgramError> {
    let magic = &instruction_data[..4];
    let mut runtime = SolanaPoolCpiRuntimeV1;
    Ok(if cfg!(feature = "pair-forest-account-evidence") && magic == b"AS8I" {
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
    })
}

/// Translatable form (target_os audit): the runtime boundary is this one call. On the deployed target it
/// is the stack-height syscall; off chain (host tests, the translator's host-target compilation)
/// every invocation is treated as transaction-level, which is what the host build did before
/// (the check was absent there). The check itself is ordinary code on every target.
#[inline(always)]
fn runtime_stack_height_v1() -> usize {
    #[cfg(target_os = "solana")]
    {
        get_stack_height()
    }
    #[cfg(not(target_os = "solana"))]
    {
        TRANSACTION_LEVEL_STACK_HEIGHT
    }
}

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
