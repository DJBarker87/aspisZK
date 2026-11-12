//! Canonical Pool V1 vault addresses and strict legacy SPL Token parsing.
//!
//! Launch supports only the original SPL Token program and its exact
//! 82-byte mint / 165-byte account images. Token-2022 and extension-bearing
//! accounts fail closed. CPI execution remains a Solana runtime boundary.

extern crate alloc;

use alloc::{vec, vec::Vec};

use solana_program::{
    account_info::AccountInfo,
    instruction::{AccountMeta, Instruction},
    program_error::ProgramError,
    pubkey::Pubkey,
};
use solana_sdk_ids::system_program;

use aspis_statement::pool_v1::PoolIdentityV1;

use crate::error::PoolV1ProgramError;

pub const LEGACY_SPL_TOKEN_PROGRAM_ID: Pubkey =
    Pubkey::from_str_const("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA");
pub const LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES: usize = 82;
pub const LEGACY_SPL_TOKEN_ACCOUNT_BYTES: usize = 165;
pub const POOL_V1_VAULT_AUTHORITY_SEED: &[u8] = b"aspis-pool-vault-authority-v1";
pub const POOL_V1_VAULT_TOKEN_ACCOUNT_SEED: &[u8] = b"aspis-pool-vault-token-v1";

const TOKEN_ACCOUNT_MINT_OFFSET: usize = 0;
const TOKEN_ACCOUNT_AUTHORITY_OFFSET: usize = 32;
const TOKEN_ACCOUNT_AMOUNT_OFFSET: usize = 64;
const TOKEN_ACCOUNT_DELEGATE_OFFSET: usize = 72;
const TOKEN_ACCOUNT_STATE_OFFSET: usize = 108;
const TOKEN_ACCOUNT_IS_NATIVE_OFFSET: usize = 109;
const TOKEN_ACCOUNT_DELEGATED_AMOUNT_OFFSET: usize = 121;
const TOKEN_ACCOUNT_CLOSE_AUTHORITY_OFFSET: usize = 129;

const TOKEN_MINT_SUPPLY_OFFSET: usize = 36;
const TOKEN_MINT_DECIMALS_OFFSET: usize = 44;
const TOKEN_MINT_INITIALIZED_OFFSET: usize = 45;
const TOKEN_MINT_FREEZE_AUTHORITY_OFFSET: usize = 46;

const SPL_TOKEN_ACCOUNT_STATE_INITIALIZED: u8 = 1;
const SPL_TOKEN_TRANSFER_CHECKED_DISCRIMINANT: u8 = 12;

pub fn pool_v1_vault_authority_address(program_id: &Pubkey, pool: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(&[POOL_V1_VAULT_AUTHORITY_SEED, pool.as_ref()], program_id)
}

pub fn pool_v1_vault_token_account_address(program_id: &Pubkey, pool: &Pubkey) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[POOL_V1_VAULT_TOKEN_ACCOUNT_SEED, pool.as_ref()],
        program_id,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LegacyMintV1 {
    pub supply: u64,
    pub decimals: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LegacyTokenAccountV1 {
    pub mint: Pubkey,
    pub authority: Pubkey,
    pub amount: u64,
    pub has_delegate: bool,
    pub is_native: bool,
    pub delegated_amount: u64,
    pub has_close_authority: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LegacyDepositTransferPlanV1 {
    pub instruction: Instruction,
    pub source: Pubkey,
    pub mint: Pubkey,
    pub vault: Pubkey,
    pub authority: Pubkey,
    pub amount: u64,
    pub source_before: u64,
    pub source_after: u64,
    pub vault_before: u64,
    pub vault_after: u64,
    pub decimals: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LegacyWithdrawalTransferPlanV1 {
    pub instruction: Instruction,
    pub mint: Pubkey,
    pub vault: Pubkey,
    pub destination: Pubkey,
    pub authority: Pubkey,
    pub amount: u64,
    pub vault_before: u64,
    pub vault_after: u64,
    pub destination_before: u64,
    pub destination_after: u64,
    pub decimals: u8,
    pub authority_bump: u8,
}

fn require_zero(bytes: &[u8]) -> Result<(), ProgramError> {
    // A `while` loop with a flag instead of `iter().any` (the native iterator has no `any`);
    // it stops at the first non-zero byte, as `any` did.
    let mut nonzero = false;
    let mut index = 0;
    while !nonzero && index < bytes.len() {
        nonzero = bytes[index] != 0;
        index += 1;
    }
    if nonzero {
        return Err(PoolV1ProgramError::UnsupportedTokenConfiguration.into());
    }
    Ok(())
}

fn token_array<const N: usize>(bytes: &[u8]) -> Result<[u8; N], ProgramError> {
    bytes
        .try_into()
        .map_err(|_| PoolV1ProgramError::InvalidTokenAccount.into())
}

fn parse_coption_pubkey(bytes: &[u8]) -> Result<Option<Pubkey>, ProgramError> {
    if bytes.len() != 36 {
        return Err(PoolV1ProgramError::InvalidTokenAccount.into());
    }
    match u32::from_le_bytes(token_array(&bytes[..4])?) {
        0 => {
            require_zero(&bytes[4..])?;
            Ok(None)
        }
        1 => Ok(Some(Pubkey::new_from_array(token_array(&bytes[4..])?))),
        _ => Err(PoolV1ProgramError::InvalidTokenAccount.into()),
    }
}

fn parse_coption_u64(bytes: &[u8]) -> Result<Option<u64>, ProgramError> {
    if bytes.len() != 12 {
        return Err(PoolV1ProgramError::InvalidTokenAccount.into());
    }
    match u32::from_le_bytes(token_array(&bytes[..4])?) {
        0 => {
            require_zero(&bytes[4..])?;
            Ok(None)
        }
        1 => Ok(Some(u64::from_le_bytes(token_array(&bytes[4..])?))),
        _ => Err(PoolV1ProgramError::InvalidTokenAccount.into()),
    }
}

pub(crate) fn parse_legacy_mint_v1(data: &[u8]) -> Result<LegacyMintV1, ProgramError> {
    if data.len() != LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES {
        return Err(PoolV1ProgramError::UnsupportedTokenConfiguration.into());
    }
    parse_coption_pubkey(&data[..36])?;
    parse_coption_pubkey(&data[TOKEN_MINT_FREEZE_AUTHORITY_OFFSET..])?;
    if data[TOKEN_MINT_INITIALIZED_OFFSET] != 1 {
        return Err(PoolV1ProgramError::InvalidMint.into());
    }
    Ok(LegacyMintV1 {
        supply: u64::from_le_bytes(token_array(
            &data[TOKEN_MINT_SUPPLY_OFFSET..TOKEN_MINT_DECIMALS_OFFSET],
        )?),
        decimals: data[TOKEN_MINT_DECIMALS_OFFSET],
    })
}

pub(crate) fn parse_legacy_token_account_v1(
    data: &[u8],
) -> Result<LegacyTokenAccountV1, ProgramError> {
    if data.len() != LEGACY_SPL_TOKEN_ACCOUNT_BYTES {
        return Err(PoolV1ProgramError::UnsupportedTokenConfiguration.into());
    }
    let delegate =
        parse_coption_pubkey(&data[TOKEN_ACCOUNT_DELEGATE_OFFSET..TOKEN_ACCOUNT_STATE_OFFSET])?;
    if data[TOKEN_ACCOUNT_STATE_OFFSET] != SPL_TOKEN_ACCOUNT_STATE_INITIALIZED {
        return Err(PoolV1ProgramError::InvalidTokenAccount.into());
    }
    let is_native = parse_coption_u64(
        &data[TOKEN_ACCOUNT_IS_NATIVE_OFFSET..TOKEN_ACCOUNT_DELEGATED_AMOUNT_OFFSET],
    )?;
    let close_authority = parse_coption_pubkey(&data[TOKEN_ACCOUNT_CLOSE_AUTHORITY_OFFSET..])?;
    Ok(LegacyTokenAccountV1 {
        mint: Pubkey::new_from_array(token_array(
            &data[TOKEN_ACCOUNT_MINT_OFFSET..TOKEN_ACCOUNT_AUTHORITY_OFFSET],
        )?),
        authority: Pubkey::new_from_array(token_array(
            &data[TOKEN_ACCOUNT_AUTHORITY_OFFSET..TOKEN_ACCOUNT_AMOUNT_OFFSET],
        )?),
        amount: u64::from_le_bytes(token_array(
            &data[TOKEN_ACCOUNT_AMOUNT_OFFSET..TOKEN_ACCOUNT_DELEGATE_OFFSET],
        )?),
        has_delegate: delegate.is_some(),
        is_native: is_native.is_some(),
        delegated_amount: u64::from_le_bytes(token_array(
            &data[TOKEN_ACCOUNT_DELEGATED_AMOUNT_OFFSET..TOKEN_ACCOUNT_CLOSE_AUTHORITY_OFFSET],
        )?),
        has_close_authority: close_authority.is_some(),
    })
}

fn require_token_owned_account(account: &AccountInfo, writable: bool) -> Result<(), ProgramError> {
    if *account.owner != LEGACY_SPL_TOKEN_PROGRAM_ID
        || account.executable
        || account.is_signer
        || account.is_writable != writable
    {
        return Err(PoolV1ProgramError::InvalidTokenAccount.into());
    }
    Ok(())
}

fn exact_five_accounts<'slice, 'info>(
    accounts: &'slice [AccountInfo<'info>],
) -> Result<[&'slice AccountInfo<'info>; 5], ProgramError> {
    // Length check and indexing instead of a slice pattern, and the ten
    // pairwise key comparisons written out in the order of the former nested loop (same first
    // failing pair, same error). The translator rejects both the slice pattern over AccountInfo
    // (Inconsistent projection) and any loop in a function that holds an AccountInfo.
    if accounts.len() != 5 {
        return Err(if accounts.len() < 5 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    let (mint, source, authority, vault, token_program) = (&accounts[0], &accounts[1], &accounts[2], &accounts[3], &accounts[4]);
    if *mint.key == *source.key
        || *mint.key == *authority.key
        || *mint.key == *vault.key
        || *mint.key == *token_program.key
        || *source.key == *authority.key
        || *source.key == *vault.key
        || *source.key == *token_program.key
        || *authority.key == *vault.key
        || *authority.key == *token_program.key
        || *vault.key == *token_program.key
    {
        return Err(PoolV1ProgramError::InvalidTokenAccount.into());
    }
    Ok([mint, source, authority, vault, token_program])
}



/// Pair-forest and legacy-state deposits share the exact vault identity,
/// token parsing and direct-owner `TransferChecked` semantics.
pub(crate) fn plan_legacy_deposit_transfer_from_identity_v1(
    program_id: &Pubkey,
    pool: &Pubkey,
    identity: &PoolIdentityV1,
    accounts: &[AccountInfo],
    amount: u32,
) -> Result<LegacyDepositTransferPlanV1, ProgramError> {
    let [mint_account, source_account, source_authority, vault_account, token_program] =
        match exact_five_accounts(accounts) {
            Ok(five) => five,
            Err(err) => return Err(err),
        };
    if identity.token_program != LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes()
        || *token_program.key != LEGACY_SPL_TOKEN_PROGRAM_ID
        || !token_program.executable
        || token_program.is_signer
        || token_program.is_writable
    {
        return Err(PoolV1ProgramError::InvalidTokenProgram.into());
    }

    let expected_mint = Pubkey::new_from_array(identity.asset_mint);
    if *mint_account.key != expected_mint {
        return Err(PoolV1ProgramError::InvalidMint.into());
    }
    require_token_owned_account(mint_account, false)?;
    let mint = {
        let data = match mint_account.try_borrow_data() {
            Ok(data) => data,
            Err(err) => return Err(err),
        };
        parse_legacy_mint_v1(&data)?
    };

    require_token_owned_account(source_account, true)?;
    require_token_owned_account(vault_account, true)?;
    if !source_authority.is_signer || source_authority.is_writable || source_authority.executable {
        return Err(PoolV1ProgramError::InvalidSourceAuthority.into());
    }

    let source = {
        let data = match source_account.try_borrow_data() {
            Ok(data) => data,
            Err(err) => return Err(err),
        };
        parse_legacy_token_account_v1(&data)?
    };
    let vault_state = {
        let data = match vault_account.try_borrow_data() {
            Ok(data) => data,
            Err(err) => return Err(err),
        };
        parse_legacy_token_account_v1(&data)?
    };
    if source.mint != expected_mint
        || vault_state.mint != expected_mint
        || source.authority != *source_authority.key
    {
        return Err(PoolV1ProgramError::InvalidTokenAccount.into());
    }
    let expected_vault = pool_v1_vault_token_account_address(program_id, pool).0;
    if *vault_account.key != expected_vault {
        return Err(PoolV1ProgramError::InvalidVaultTokenAddress.into());
    }
    let expected_vault_authority = pool_v1_vault_authority_address(program_id, pool).0;
    if vault_state.authority != expected_vault_authority {
        return Err(PoolV1ProgramError::InvalidVaultAuthority.into());
    }
    // The launch vault has no delegate/close/native side channels. In
    // particular wrapped-native reserve semantics are deferred rather than
    // silently folded into the conservation invariant.
    if vault_state.has_delegate
        || vault_state.is_native
        || vault_state.delegated_amount != 0
        || vault_state.has_close_authority
    {
        return Err(PoolV1ProgramError::UnsupportedTokenConfiguration.into());
    }

    let amount = u64::from(amount);
    let source_after = match source
        .amount
        .checked_sub(amount) {
        Some(value) => value,
        None => return Err(PoolV1ProgramError::InsufficientDepositFunds.into()),
    };
    let vault_after = match vault_state
        .amount
        .checked_add(amount) {
        Some(value) => value,
        None => return Err(PoolV1ProgramError::ArithmeticOverflow.into()),
    };
    let mut data = Vec::with_capacity(10);
    data.push(SPL_TOKEN_TRANSFER_CHECKED_DISCRIMINANT);
    data.extend_from_slice(&amount.to_le_bytes());
    data.push(mint.decimals);
    let instruction = Instruction {
        program_id: LEGACY_SPL_TOKEN_PROGRAM_ID,
        accounts: vec![
            AccountMeta::new(*source_account.key, false),
            AccountMeta::new_readonly(*mint_account.key, false),
            AccountMeta::new(*vault_account.key, false),
            AccountMeta::new_readonly(*source_authority.key, true),
        ],
        data,
    };
    Ok(LegacyDepositTransferPlanV1 {
        instruction,
        source: *source_account.key,
        mint: *mint_account.key,
        vault: *vault_account.key,
        authority: *source_authority.key,
        amount,
        source_before: source.amount,
        source_after,
        vault_before: vault_state.amount,
        vault_after,
        decimals: mint.decimals,
    })
}

pub(crate) fn exact_transfer_account_infos_v1<'a>(
    accounts: &[AccountInfo<'a>],
) -> Result<[AccountInfo<'a>; 5], ProgramError> {
    // The translator rejects the array pattern over the returned references and the clones
    // out of it (Unimplemented). `exact_five_accounts` returns references to accounts[0..5] in order, so the same
    // check runs first and the same five accounts are cloned from the slice by index in the same output order.
    if let Err(err) = exact_five_accounts(accounts) {
        return Err(err);
    }
    // [mint, source, authority, vault, token_program] = accounts[0..5]
    Ok([
        accounts[1].clone(),
        accounts[0].clone(),
        accounts[3].clone(),
        accounts[2].clone(),
        accounts[4].clone(),
    ])
}

fn exact_five_withdrawal_accounts<'slice, 'info>(
    accounts: &'slice [AccountInfo<'info>],
) -> Result<[&'slice AccountInfo<'info>; 5], ProgramError> {
    // Length check and indexing instead of a slice pattern, and the ten
    // pairwise key comparisons written out in the order of the former nested loop (same first
    // failing pair, same error). The translator rejects both the slice pattern over AccountInfo
    // (Inconsistent projection) and any loop in a function that holds an AccountInfo.
    if accounts.len() != 5 {
        return Err(if accounts.len() < 5 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    let (mint, vault, destination, vault_authority, token_program) = (&accounts[0], &accounts[1], &accounts[2], &accounts[3], &accounts[4]);
    if *mint.key == *vault.key
        || *mint.key == *destination.key
        || *mint.key == *vault_authority.key
        || *mint.key == *token_program.key
        || *vault.key == *destination.key
        || *vault.key == *vault_authority.key
        || *vault.key == *token_program.key
        || *destination.key == *vault_authority.key
        || *destination.key == *token_program.key
        || *vault_authority.key == *token_program.key
    {
        return Err(PoolV1ProgramError::InvalidTokenAccount.into());
    }
    Ok([mint, vault, destination, vault_authority, token_program])
}



/// Pool-only bump hints for the two constant-seed custody PDAs (pair-forest
/// R1 withdrawal). They are carried in Pool instruction data only; the master
/// format and the verifier are unchanged.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct VaultBumpHintsV1 {
    pub vault_authority: u8,
    pub vault_token_account: u8,
}

/// Pair-state and legacy-state withdrawal paths share the exact vault
/// identity and custody rules. Keeping the planner on the sealed Pool
/// identity avoids duplicating token-account parsing or transfer semantics.
pub(crate) fn plan_legacy_withdrawal_transfer_from_identity_v1(
    program_id: &Pubkey,
    pool: &Pubkey,
    identity: &PoolIdentityV1,
    accounts: &[AccountInfo],
    destination: &Pubkey,
    amount: u32,
    bump_hints: Option<VaultBumpHintsV1>,
) -> Result<LegacyWithdrawalTransferPlanV1, ProgramError> {
    let [mint_account, vault_account, destination_account, vault_authority, token_program] =
        match exact_five_withdrawal_accounts(accounts) {
            Ok(five) => five,
            Err(err) => return Err(err),
        };
    if amount == 0 {
        return Err(PoolV1ProgramError::InvalidWithdrawalAmount.into());
    }
    if identity.token_program != LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes()
        || *token_program.key != LEGACY_SPL_TOKEN_PROGRAM_ID
        || !token_program.executable
        || token_program.is_signer
        || token_program.is_writable
    {
        return Err(PoolV1ProgramError::InvalidTokenProgram.into());
    }

    let expected_mint = Pubkey::new_from_array(identity.asset_mint);
    if *mint_account.key != expected_mint {
        return Err(PoolV1ProgramError::InvalidMint.into());
    }
    require_token_owned_account(mint_account, false)?;
    let mint = {
        let data = match mint_account.try_borrow_data() {
            Ok(data) => data,
            Err(err) => return Err(err),
        };
        parse_legacy_mint_v1(&data)?
    };

    require_token_owned_account(vault_account, true)?;
    require_token_owned_account(destination_account, true)?;
    // Translatable form (emitter line break): the authority derivation and check, and the plan built from the checked
    // values, are helpers in the same order; the emitted body was nested deep enough that the emitter broke a match
    // arm across lines ("unexpected identifier; expected '=>'").
    // The authority's fields are read here and passed as values (a helper taking the account reference made the
    // later vault-address match fail with nested borrows, run X2c-pool-c6). `data_is_empty` is evaluated before the
    // helper's checks instead of last in their `||` chain: it reads the data length only and cannot fail.
    let (expected_authority, authority_bump) = match withdrawal_vault_authority_v1(
        program_id,
        pool,
        *vault_authority.key,
        *vault_authority.owner,
        vault_authority.executable,
        vault_authority.is_signer,
        vault_authority.is_writable,
        vault_authority.data_is_empty(),
        bump_hints,
    ) {
        Ok(value) => value,
        Err(err) => return Err(err),
    };
    if *destination_account.key != *destination {
        return Err(PoolV1ProgramError::InvalidDestinationTokenAccount.into());
    }

    let vault_state = {
        let data = match vault_account.try_borrow_data() {
            Ok(data) => data,
            Err(err) => return Err(err),
        };
        parse_legacy_token_account_v1(&data)?
    };
    let destination_state = {
        let data = match destination_account.try_borrow_data() {
            Ok(data) => data,
            Err(err) => return Err(err),
        };
        parse_legacy_token_account_v1(&data)?
    };
    if !withdrawal_vault_address_ok_v1(program_id, pool, *vault_account.key, bump_hints) {
        return Err(PoolV1ProgramError::InvalidVaultTokenAddress.into());
    }
    if vault_state.mint != expected_mint
        || destination_state.mint != expected_mint
        || vault_state.authority != expected_authority
    {
        return Err(PoolV1ProgramError::InvalidTokenAccount.into());
    }
    if vault_state.has_delegate
        || vault_state.is_native
        || vault_state.delegated_amount != 0
        || vault_state.has_close_authority
        || destination_state.is_native
    {
        return Err(PoolV1ProgramError::UnsupportedTokenConfiguration.into());
    }

    withdrawal_plan_from_checked_values_v1(
        *mint_account.key,
        *vault_account.key,
        *destination_account.key,
        *vault_authority.key,
        amount,
        vault_state.amount,
        destination_state.amount,
        mint.decimals,
        authority_bump,
    )
}

/// The vault-authority part of `plan_legacy_withdrawal_transfer_from_identity_v1` (frozen order and errors),
/// over the authority account's key, owner and flags as values.
#[allow(clippy::too_many_arguments)]
fn withdrawal_vault_authority_v1(
    program_id: &Pubkey,
    pool: &Pubkey,
    authority_key: Pubkey,
    authority_owner: Pubkey,
    authority_executable: bool,
    authority_is_signer: bool,
    authority_is_writable: bool,
    authority_data_is_empty: bool,
    bump_hints: Option<VaultBumpHintsV1>,
) -> Result<(Pubkey, u8), ProgramError> {
    // With hints (B4-style, Pool-only): one `create_program_address` each.
    // A hinted non-canonical authority cannot pass, because the vault token
    // account (authenticated below) records the canonical authority, and the
    // Pool creates the vault token account only at its canonical bump.
    let (expected_authority, authority_bump) = match bump_hints {
        Some(hints) => (
            if crate::registry::stored_bump_address_matches(
                &[
                    POOL_V1_VAULT_AUTHORITY_SEED,
                    pool.as_ref(),
                    &[hints.vault_authority],
                ],
                program_id,
                &authority_key,
            ) {
                authority_key
            } else {
                return Err(PoolV1ProgramError::InvalidVaultAuthority.into());
            },
            hints.vault_authority,
        ),
        None => pool_v1_vault_authority_address(program_id, pool),
    };
    if authority_key != expected_authority
        || authority_owner != system_program::id()
        || authority_executable
        || authority_is_signer
        || authority_is_writable
        || !authority_data_is_empty
    {
        return Err(PoolV1ProgramError::InvalidVaultAuthority.into());
    }
    Ok((expected_authority, authority_bump))
}

/// The vault token account address check of `plan_legacy_withdrawal_transfer_from_identity_v1`, over the
/// vault's key as a value.
fn withdrawal_vault_address_ok_v1(
    program_id: &Pubkey,
    pool: &Pubkey,
    vault_key: Pubkey,
    bump_hints: Option<VaultBumpHintsV1>,
) -> bool {
    match bump_hints {
        Some(hints) => crate::registry::stored_bump_address_matches(
            &[
                POOL_V1_VAULT_TOKEN_ACCOUNT_SEED,
                pool.as_ref(),
                &[hints.vault_token_account],
            ],
            program_id,
            &vault_key,
        ),
        None => vault_key == pool_v1_vault_token_account_address(program_id, pool).0,
    }
}

/// The tail of `plan_legacy_withdrawal_transfer_from_identity_v1` over plain values (frozen order and errors).
#[allow(clippy::too_many_arguments)]
fn withdrawal_plan_from_checked_values_v1(
    mint_key: Pubkey,
    vault_key: Pubkey,
    destination_key: Pubkey,
    authority_key: Pubkey,
    amount: u32,
    vault_amount: u64,
    destination_amount: u64,
    decimals: u8,
    authority_bump: u8,
) -> Result<LegacyWithdrawalTransferPlanV1, ProgramError> {
    let amount = u64::from(amount);
    let vault_after = match vault_amount
        .checked_sub(amount) {
        Some(value) => value,
        None => return Err(PoolV1ProgramError::InsufficientVaultFunds.into()),
    };
    let destination_after = match destination_amount
        .checked_add(amount) {
        Some(value) => value,
        None => return Err(PoolV1ProgramError::ArithmeticOverflow.into()),
    };
    let mut data = Vec::with_capacity(10);
    data.push(SPL_TOKEN_TRANSFER_CHECKED_DISCRIMINANT);
    data.extend_from_slice(&amount.to_le_bytes());
    data.push(decimals);
    let instruction = Instruction {
        program_id: LEGACY_SPL_TOKEN_PROGRAM_ID,
        accounts: vec![
            AccountMeta::new(vault_key, false),
            AccountMeta::new_readonly(mint_key, false),
            AccountMeta::new(destination_key, false),
            AccountMeta::new_readonly(authority_key, true),
        ],
        data,
    };
    Ok(LegacyWithdrawalTransferPlanV1 {
        instruction,
        mint: mint_key,
        vault: vault_key,
        destination: destination_key,
        authority: authority_key,
        amount,
        vault_before: vault_amount,
        vault_after,
        destination_before: destination_amount,
        destination_after,
        decimals,
        authority_bump,
    })
}

pub(crate) fn exact_withdrawal_transfer_account_infos_v1<'a>(
    accounts: &[AccountInfo<'a>],
) -> Result<[AccountInfo<'a>; 5], ProgramError> {
    // As `exact_transfer_account_infos_v1`; `exact_five_withdrawal_accounts` returns
    // references to accounts[0..5] in order.
    if let Err(err) = exact_five_withdrawal_accounts(accounts) {
        return Err(err);
    }
    // [mint, vault, destination, vault_authority, token_program] = accounts[0..5]
    Ok([
        accounts[1].clone(),
        accounts[0].clone(),
        accounts[2].clone(),
        accounts[3].clone(),
        accounts[4].clone(),
    ])
}

/// Re-read both balances after the withdrawal CPI.  The Pool state and
/// nullifier marker are not persisted until this exact delta has authenticated.
pub(crate) fn validate_exact_withdrawal_delta_v1(
    accounts: &[AccountInfo],
    plan: &LegacyWithdrawalTransferPlanV1,
) -> Result<(), ProgramError> {
    let [mint_account, vault_account, destination_account, vault_authority, token_program] =
        match exact_five_withdrawal_accounts(accounts) {
            Ok(five) => five,
            Err(err) => return Err(err),
        };
    if *mint_account.key != plan.mint
        || *vault_account.key != plan.vault
        || *destination_account.key != plan.destination
        || *vault_authority.key != plan.authority
        || *token_program.key != LEGACY_SPL_TOKEN_PROGRAM_ID
    {
        return Err(PoolV1ProgramError::TokenBalanceDeltaMismatch.into());
    }
    let vault_state = {
        let data = match vault_account.try_borrow_data() {
            Ok(data) => data,
            Err(err) => return Err(err),
        };
        parse_legacy_token_account_v1(&data)?
    };
    let destination = {
        let data = match destination_account.try_borrow_data() {
            Ok(data) => data,
            Err(err) => return Err(err),
        };
        parse_legacy_token_account_v1(&data)?
    };
    if vault_state.mint != plan.mint
        || destination.mint != plan.mint
        || vault_state.authority != plan.authority
        || vault_state.amount != plan.vault_after
        || destination.amount != plan.destination_after
    {
        return Err(PoolV1ProgramError::TokenBalanceDeltaMismatch.into());
    }
    Ok(())
}

/// Re-read balances after CPI and require the exact requested debit/credit.
/// Any mismatch returns before the Pool state/history bytes are persisted.
pub(crate) fn validate_exact_deposit_delta_v1(
    accounts: &[AccountInfo],
    plan: &LegacyDepositTransferPlanV1,
) -> Result<(), ProgramError> {
    let [mint_account, source_account, source_authority, vault_account, token_program] =
        match exact_five_accounts(accounts) {
            Ok(five) => five,
            Err(err) => return Err(err),
        };
    if *mint_account.key != plan.mint
        || *source_account.key != plan.source
        || *source_authority.key != plan.authority
        || *vault_account.key != plan.vault
        || *token_program.key != LEGACY_SPL_TOKEN_PROGRAM_ID
    {
        return Err(PoolV1ProgramError::TokenBalanceDeltaMismatch.into());
    }
    let source = {
        let data = match source_account.try_borrow_data() {
            Ok(data) => data,
            Err(err) => return Err(err),
        };
        parse_legacy_token_account_v1(&data)?
    };
    let vault_state = {
        let data = match vault_account.try_borrow_data() {
            Ok(data) => data,
            Err(err) => return Err(err),
        };
        parse_legacy_token_account_v1(&data)?
    };
    if source.mint != plan.mint
        || vault_state.mint != plan.mint
        || source.authority != plan.authority
        || source.amount != plan.source_after
        || vault_state.amount != plan.vault_after
    {
        return Err(PoolV1ProgramError::TokenBalanceDeltaMismatch.into());
    }
    Ok(())
}

#[cfg(test)]
pub(crate) fn write_token_amount_for_test(
    account: &AccountInfo,
    amount: u64,
) -> Result<(), ProgramError> {
    let mut data = account.try_borrow_mut_data()?;
    if data.len() != LEGACY_SPL_TOKEN_ACCOUNT_BYTES {
        return Err(PoolV1ProgramError::InvalidTokenAccount.into());
    }
    data[TOKEN_ACCOUNT_AMOUNT_OFFSET..TOKEN_ACCOUNT_DELEGATE_OFFSET]
        .copy_from_slice(&amount.to_le_bytes());
    Ok(())
}
