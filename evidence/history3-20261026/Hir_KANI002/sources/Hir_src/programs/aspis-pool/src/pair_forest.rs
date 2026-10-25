//! Production-inactive Solana account plumbing for the eight-lane pair forest.
//!
//! This module is compiled only under the explicit
//! `pair-forest-account-evidence` feature. It defines exact initialization and
//! permissionless checkpoint instructions plus a vault-backed deterministic
//! lane deposit and a compact one-terminal spend caller. The spend caller is
//! still inactive by default and requires a separately reviewed selected
//! verifier ASQ8 handler. The checkpoint reads all eight lane PDAs in one
//! invocation and computes the seven frozen Pool Poseidon parents internally.

extern crate alloc;

use alloc::{boxed::Box, vec::Vec};
use aspis_core::field::M31;

use aspis_statement::{
    decode_digest_canonical, encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_pair_forest_checkpoint_v1, decode_pool_v1_pair_forest_lane_state_v1,
        decode_pool_v1_pair_forest_master_v1, decode_pool_v1_pair_forest_terminal_request_v1,
        decode_pool_v1_pair_forest_terminal_statement_v1, encode_pool_v1_pair_forest_checkpoint_v1,
        encode_pool_v1_pair_forest_lane_state_v1, encode_pool_v1_pair_forest_master_v1,
        encode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_forest_terminal_result_v1, plan_pool_v1_pair_forest_checkpoint_v1,
        pool_v1_note_commitment, pool_v1_pair_forest_deposit_lane_v1, pool_v1_tree_parent,
        root_history_location, validate_pool_v1_pair_forest_terminal_result_against_statement_v1,
        AppendOneV1, IncrementalMerkleTreeV1, PoolIdentityV1, PoolV1NullifierMarkerV1,
        PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1, PoolV1PairForestMasterV1,
        PoolV1PairForestTerminalCommonV1, PoolV1PairForestTerminalPaymentV1,
        PoolV1PairForestTerminalRequestV1, PoolV1PairForestTerminalStatementV1,
        PoolV1PairLeafWitnessV1, POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_PAIR_CAPACITY,
        POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
        POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_COUNT,
        POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES, POOL_V1_PAIR_FOREST_LANE_MAGIC,
        POOL_V1_PAIR_FOREST_LANE_VERSION, POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
        POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES, POOL_V1_PAIR_TREE_DEPTH,
        POOL_V1_ROOT_HISTORY_CAPACITY, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        POOL_V1_ROOT_HISTORY_PAGE_SEED, POOL_V1_TREE_HASH_VERSION, POOL_V1_TREE_STATE_MAGIC,
        POOL_V1_TREE_STATE_VERSION,
    },
    poseidon2::Digest,
};
use solana_program::{
    account_info::AccountInfo, entrypoint::ProgramResult, program_error::ProgramError,
    pubkey::Pubkey, rent::Rent,
};

use crate::{
    deposit::DepositRequestV1,
    deposit_transport::{
        decode_deposit_instruction_with_magic_v1, encode_deposit_instruction_v1,
        DepositInstructionFormatErrorV1,
    },
    empty_roots::POOL_V1_PAIR_EMPTY_ROOTS,
    error::PoolV1ProgramError,
    history::{
        append_roots_unchecked, pool_v1_root_page_address, read_retained_root,
        require_program_account, validate_root_page_bytes, write_new_page_unchecked,
        RootPageHeaderV1,
    },
    instruction::{
        decode_initialize_instruction_v1, encode_initialize_instruction_v1,
        PoolInstructionFormatErrorV1, POOL_V1_INITIALIZE_INSTRUCTION_BYTES,
        POOL_V1_INITIALIZE_INSTRUCTION_MAGIC, POOL_V1_INSTRUCTION_VERSION,
    },
    nullifier::plan_pair_forest_nullifier_marker_consumption_v1,
    pair_forest_dispatch::{
        dispatch_pair_forest_terminal_readonly_v1, AuthenticatedPairForestResultV1,
    },
    processor::{
        create_or_allocate_pda, create_pair_forest_nullifier_marker_if_needed_v1,
        initialize_vault_account,
        plan_fresh_program_pda, plan_vault_initialization, require_payer_and_system_program,
        require_token_program_account, require_unique_accounts, FreshPdaPreparationV1,
        PoolCpiRuntimeV1,
    },
    state::PoolInitializationV1,
    vault::{
        exact_transfer_account_infos_v1, exact_withdrawal_transfer_account_infos_v1,
        parse_legacy_mint_v1, plan_legacy_deposit_transfer_from_identity_v1,
        plan_legacy_withdrawal_transfer_from_identity_v1, validate_exact_deposit_delta_v1,
        validate_exact_withdrawal_delta_v1, LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES,
        LEGACY_SPL_TOKEN_PROGRAM_ID, POOL_V1_VAULT_AUTHORITY_SEED, VaultBumpHintsV1,
    },
};

pub const POOL_V1_PAIR_FOREST_MASTER_SEED: &[u8] = b"aspis-pair-forest-master-v1";
pub const POOL_V1_PAIR_FOREST_LANE_SEED: &[u8] = b"aspis-pair-forest-lane-v1";
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_SEED: &[u8] = b"aspis-pair-forest-checkpoint-v1";

pub const POOL_V1_PAIR_FOREST_INITIALIZE_INSTRUCTION_MAGIC: [u8; 4] = *b"AS8I";
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC: [u8; 4] = *b"AS8C";
pub const POOL_V1_PAIR_FOREST_DEPOSIT_INSTRUCTION_MAGIC: [u8; 4] = *b"AS8D";
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_BYTES: usize = 8;
pub const POOL_V1_PAIR_FOREST_INITIALIZE_ACCOUNT_COUNT: usize = 14;
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_COUNT: usize = 12;

/// B4 bump hints appended to the terminal (ASQ8 / audit ASF8) instruction
/// data: `[current_page, next_page, vault_authority, vault_token_account]`.
///
/// The Pool instruction data is `request || hints`; the verifier still
/// receives only the re-encoded request (or, on the ASF8 audit route, the
/// exact statement without the suffix). `current_page` authenticates the
/// lane's current root page (page 0 in genesis mode); `next_page` the zeroed
/// next page on rollover; the two vault bytes the withdrawal custody PDAs.
/// Each is checked with one `create_program_address`; a byte the route does
/// not use (next page without rollover, vault bytes on a transfer) must be
/// zero. Bump 0 is never a canonical bump (`find_program_address` stops at 1),
/// so zero is unambiguous.
pub const POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES: usize = 4;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PoolV1PairForestTerminalBumpHintsV1 {
    pub current_page: u8,
    pub next_page: u8,
    pub vault_authority: u8,
    pub vault_token_account: u8,
}

impl PoolV1PairForestTerminalBumpHintsV1 {
    pub fn encode(self) -> [u8; POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES] {
        [
            self.current_page,
            self.next_page,
            self.vault_authority,
            self.vault_token_account,
        ]
    }

    fn vault(self) -> VaultBumpHintsV1 {
        VaultBumpHintsV1 {
            vault_authority: self.vault_authority,
            vault_token_account: self.vault_token_account,
        }
    }
}

/// Split `body || hints`. The body keeps its own exact-length decoder.
pub fn split_pair_forest_terminal_bump_hints_v1(
    instruction_data: &[u8],
) -> Result<(&[u8], PoolV1PairForestTerminalBumpHintsV1), ProgramError> {
    let split = instruction_data
        .len()
        .checked_sub(POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES)
        .ok_or(ProgramError::InvalidInstructionData)?;
    let (body, hints) = instruction_data.split_at(split);
    Ok((
        body,
        PoolV1PairForestTerminalBumpHintsV1 {
            current_page: hints[0],
            next_page: hints[1],
            vault_authority: hints[2],
            vault_token_account: hints[3],
        },
    ))
}

/// Client-side derivation of the canonical hints for one terminal spend on a
/// lane whose tree holds `next_leaf_index` leaves. Off chain only: it runs the
/// canonical searches that the Pool no longer performs.
#[cfg(not(target_os = "solana"))]
pub fn pool_v1_pair_forest_terminal_bump_hints_v1(
    program_id: &Pubkey,
    master: &Pubkey,
    lane: &Pubkey,
    next_leaf_index: u64,
    withdrawal: bool,
) -> PoolV1PairForestTerminalBumpHintsV1 {
    let current = root_history_location(next_leaf_index);
    let next = root_history_location(next_leaf_index + 1);
    let current_page = pool_v1_root_page_address(program_id, lane, current.page_number).1;
    let next_page = if current.page_number == next.page_number {
        0
    } else {
        pool_v1_root_page_address(program_id, lane, next.page_number).1
    };
    let (vault_authority, vault_token_account) = if withdrawal {
        (
            crate::vault::pool_v1_vault_authority_address(program_id, master).1,
            crate::vault::pool_v1_vault_token_account_address(program_id, master).1,
        )
    } else {
        (0, 0)
    };
    PoolV1PairForestTerminalBumpHintsV1 {
        current_page,
        next_page,
        vault_authority,
        vault_token_account,
    }
}

/// Exact terminal instruction data `request || hints` (client side).
pub fn encode_pair_forest_terminal_instruction_data_v1(
    request: &[u8],
    hints: PoolV1PairForestTerminalBumpHintsV1,
) -> Vec<u8> {
    let mut data = Vec::with_capacity(request.len() + POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES);
    data.extend_from_slice(request);
    data.extend_from_slice(&hints.encode());
    data
}

const FOREST_MASTER_ACCOUNT_INDEX: usize = 0;
const FOREST_FIRST_LANE_ACCOUNT_INDEX: usize = 1;
const FOREST_MINT_OR_CHECKPOINT_ACCOUNT_INDEX: usize = 9;
const FOREST_INIT_VAULT_ACCOUNT_INDEX: usize = 10;
const FOREST_INIT_TOKEN_PROGRAM_ACCOUNT_INDEX: usize = 11;
const FOREST_INIT_PAYER_ACCOUNT_INDEX: usize = 12;
const FOREST_INIT_SYSTEM_ACCOUNT_INDEX: usize = 13;
const FOREST_CHECKPOINT_PAYER_ACCOUNT_INDEX: usize = 10;
const FOREST_CHECKPOINT_SYSTEM_ACCOUNT_INDEX: usize = 11;

const FOREST_DEPOSIT_MASTER_ACCOUNT_INDEX: usize = 0;
const FOREST_DEPOSIT_LANE_ACCOUNT_INDEX: usize = 1;
const FOREST_DEPOSIT_CURRENT_PAGE_ACCOUNT_INDEX: usize = 2;
const FOREST_DEPOSIT_SAME_PAGE_ACCOUNT_COUNT: usize = 8;
const FOREST_DEPOSIT_GENESIS_PAGE_ACCOUNT_COUNT: usize = 10;
const FOREST_DEPOSIT_ROLLOVER_ACCOUNT_COUNT: usize = 11;

pub fn encode_pair_forest_initialize_instruction_v1(
    initialization: &PoolInitializationV1,
) -> Result<[u8; POOL_V1_INITIALIZE_INSTRUCTION_BYTES], PoolInstructionFormatErrorV1> {
    let mut encoded = encode_initialize_instruction_v1(initialization)?;
    encoded[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_INITIALIZE_INSTRUCTION_MAGIC);
    encoded[5] = POOL_V1_PAIR_FOREST_LANE_COUNT as u8;
    encoded[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    Ok(encoded)
}

pub fn decode_pair_forest_initialize_instruction_v1(
    bytes: &[u8],
) -> Result<PoolInitializationV1, PoolInstructionFormatErrorV1> {
    if bytes.len() != POOL_V1_INITIALIZE_INSTRUCTION_BYTES {
        return Err(PoolInstructionFormatErrorV1::WrongLength);
    }
    if bytes[..4] != POOL_V1_PAIR_FOREST_INITIALIZE_INSTRUCTION_MAGIC {
        return Err(PoolInstructionFormatErrorV1::WrongMagic);
    }
    if bytes[4] != POOL_V1_INSTRUCTION_VERSION {
        return Err(PoolInstructionFormatErrorV1::WrongVersion);
    }
    if bytes[5] != POOL_V1_PAIR_FOREST_LANE_COUNT as u8
        || bytes[6] != POOL_V1_DIGEST_ENCODING_VERSION
    {
        return Err(PoolInstructionFormatErrorV1::NonCanonicalField);
    }
    if bytes[7] != 0 {
        return Err(PoolInstructionFormatErrorV1::NonZeroReserved);
    }
    let mut legacy = [0u8; POOL_V1_INITIALIZE_INSTRUCTION_BYTES];
    legacy.copy_from_slice(bytes);
    legacy[..4].copy_from_slice(&POOL_V1_INITIALIZE_INSTRUCTION_MAGIC);
    legacy[5..8].fill(0);
    decode_initialize_instruction_v1(&legacy)
}

pub fn encode_pair_forest_checkpoint_instruction_v1(
) -> [u8; POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_BYTES] {
    [
        POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC[0],
        POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC[1],
        POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC[2],
        POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC[3],
        POOL_V1_INSTRUCTION_VERSION,
        POOL_V1_PAIR_FOREST_LANE_COUNT as u8,
        POOL_V1_DIGEST_ENCODING_VERSION,
        0,
    ]
}

pub fn decode_pair_forest_checkpoint_instruction_v1(bytes: &[u8]) -> ProgramResult {
    if bytes != encode_pair_forest_checkpoint_instruction_v1() {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(())
}

pub fn encode_pair_forest_deposit_instruction_v1(
    request: &DepositRequestV1<'_>,
) -> Result<Vec<u8>, DepositInstructionFormatErrorV1> {
    let mut encoded = encode_deposit_instruction_v1(request)?.as_bytes().to_vec();
    encoded[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_DEPOSIT_INSTRUCTION_MAGIC);
    Ok(encoded)
}

pub fn decode_pair_forest_deposit_instruction_v1(
    bytes: &[u8],
) -> Result<DepositRequestV1<'_>, DepositInstructionFormatErrorV1> {
    decode_deposit_instruction_with_magic_v1(bytes, POOL_V1_PAIR_FOREST_DEPOSIT_INSTRUCTION_MAGIC)
}

/// Exact frozen binary tree over lanes 0 through 7. The order is part of the
/// checkpoint ABI and uses the existing Pool parent primitive seven times.
pub fn pool_v1_pair_forest_global_root_v1(
    lane_roots: &[Digest; POOL_V1_PAIR_FOREST_LANE_COUNT],
) -> Digest {
    let level_one = [
        pool_v1_tree_parent(&lane_roots[0], &lane_roots[1]),
        pool_v1_tree_parent(&lane_roots[2], &lane_roots[3]),
        pool_v1_tree_parent(&lane_roots[4], &lane_roots[5]),
        pool_v1_tree_parent(&lane_roots[6], &lane_roots[7]),
    ];
    let level_two = [
        pool_v1_tree_parent(&level_one[0], &level_one[1]),
        pool_v1_tree_parent(&level_one[2], &level_one[3]),
    ];
    pool_v1_tree_parent(&level_two[0], &level_two[1])
}

pub fn pool_v1_pair_forest_master_address(
    program_id: &Pubkey,
    asset_mint: &Pubkey,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[POOL_V1_PAIR_FOREST_MASTER_SEED, asset_mint.as_ref()],
        program_id,
    )
}

pub fn pool_v1_pair_forest_lane_address(
    program_id: &Pubkey,
    master: &Pubkey,
    lane_id: u8,
) -> Result<(Pubkey, u8), ProgramError> {
    if usize::from(lane_id) >= POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(ProgramError::InvalidSeeds);
    }
    Ok(Pubkey::find_program_address(
        &[POOL_V1_PAIR_FOREST_LANE_SEED, master.as_ref(), &[lane_id]],
        program_id,
    ))
}

pub fn pool_v1_pair_forest_checkpoint_address(
    program_id: &Pubkey,
    master: &Pubkey,
    checkpoint_sequence: u64,
) -> (Pubkey, u8) {
    Pubkey::find_program_address(
        &[
            POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,
            master.as_ref(),
            &checkpoint_sequence.to_le_bytes(),
        ],
        program_id,
    )
}

/// Lane-local root-history identity. Existing root-page bytes remain unchanged:
/// their `pool` field is the canonical lane-state PDA, not the forest master.
pub fn pool_v1_pair_forest_lane_root_page_address(
    program_id: &Pubkey,
    master: &Pubkey,
    lane_id: u8,
    page_number: u64,
) -> Result<(Pubkey, u8), ProgramError> {
    let lane = pool_v1_pair_forest_lane_address(program_id, master, lane_id)?.0;
    Ok(pool_v1_root_page_address(program_id, &lane, page_number))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlannedPairForestCheckpointAccountsV1 {
    pub master: Pubkey,
    pub checkpoint: Pubkey,
    pub lane_sequences: [u64; POOL_V1_PAIR_FOREST_LANE_COUNT],
    pub next_master_image: [u8; POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES],
    pub checkpoint_image: [u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES],
}

fn require_exact_account_count(accounts: &[AccountInfo<'_>], expected: usize) -> ProgramResult {
    if accounts.len() != expected {
        return Err(if accounts.len() < expected {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    Ok(())
}

fn require_forest_mint_account(
    initialization: &PoolInitializationV1,
    mint: &AccountInfo<'_>,
) -> ProgramResult {
    if mint.key.to_bytes() != initialization.asset_mint
        || initialization.token_program != LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes()
        || mint.owner != &LEGACY_SPL_TOKEN_PROGRAM_ID
        || mint.executable
        || mint.is_signer
        || mint.is_writable
        || mint.data_len() != LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES
    {
        return Err(PoolV1ProgramError::InvalidMint.into());
    }
    parse_legacy_mint_v1(&mint.try_borrow_data()?)?;
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

fn genesis_lane_state(master: &Pubkey, lane_id: u8, bump: u8) -> PoolV1PairForestLaneStateV1 {
    PoolV1PairForestLaneStateV1 {
        bump,
        master: master.to_bytes(),
        lane_id,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index: 0,
            root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
            frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
        },
    }
}

fn decode_master_account(
    program_id: &Pubkey,
    account: &AccountInfo<'_>,
    writable: bool,
) -> Result<PoolV1PairForestMasterV1, ProgramError> {
    require_program_account(account, program_id, writable)?;
    if account.is_signer {
        return Err(ProgramError::InvalidAccountData);
    }
    let master = decode_pool_v1_pair_forest_master_v1(&account.try_borrow_data()?)
        .map_err(|_| PoolV1ProgramError::InvalidAccountType)?;
    // Stored canonical bump (G_R1.8): initialization persists the canonical
    // `find_program_address` bump and the Pool signs only with canonical bumps,
    // so one derivation authenticates this Pool-owned image without a search.
    if !master_address_matches(program_id, &master, account.key)
        || master.identity.pool != account.key.to_bytes()
    {
        return Err(PoolV1ProgramError::InvalidPoolStateAddress.into());
    }
    Ok(master)
}

/// `key == create_program_address(master seeds || stored bump)`.
fn master_address_matches(
    program_id: &Pubkey,
    master: &PoolV1PairForestMasterV1,
    key: &Pubkey,
) -> bool {
    crate::registry::stored_bump_address_matches(
        &[
            POOL_V1_PAIR_FOREST_MASTER_SEED,
            &master.identity.asset_mint,
            &[master.bump],
        ],
        program_id,
        key,
    )
}

/// `key == create_program_address(lane seeds || stored bump)`.
fn lane_address_matches(
    program_id: &Pubkey,
    master: &Pubkey,
    lane_id: u8,
    bump: u8,
    key: &Pubkey,
) -> Result<bool, ProgramError> {
    if usize::from(lane_id) >= POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(ProgramError::InvalidSeeds);
    }
    Ok(crate::registry::stored_bump_address_matches(
        &[
            POOL_V1_PAIR_FOREST_LANE_SEED,
            master.as_ref(),
            &[lane_id],
            &[bump],
        ],
        program_id,
        key,
    ))
}

/// The stored lane bump byte of an exact-size image, if any. Used before the
/// full decode so that the address check keeps its place ahead of the image
/// checks.
fn stored_lane_bump(account: &AccountInfo<'_>) -> Result<Option<u8>, ProgramError> {
    let data = account.try_borrow_data()?;
    Ok((data.len() == POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES).then(|| data[72]))
}

fn decode_lane_account(
    program_id: &Pubkey,
    master: &Pubkey,
    expected_lane: u8,
    account: &AccountInfo<'_>,
    writable: bool,
) -> Result<PoolV1PairForestLaneStateV1, ProgramError> {
    require_program_account(account, program_id, writable)?;
    // Stored canonical bump (G_R1.8). On a mismatch the canonical search runs
    // only to reproduce the previous rejection codes: a non-canonical key is
    // an address error, a canonical key with a wrong stored bump is a state
    // error after decoding.
    let stored = stored_lane_bump(account)?;
    let fast = match stored {
        Some(bump) => lane_address_matches(program_id, master, expected_lane, bump, account.key)?,
        None => false,
    };
    let (expected, bump) = if fast {
        (*account.key, stored.unwrap_or_default())
    } else {
        pool_v1_pair_forest_lane_address(program_id, master, expected_lane)?
    };
    if account.is_signer || account.key != &expected {
        return Err(PoolV1ProgramError::InvalidPoolStateAddress.into());
    }
    let lane = decode_pool_v1_pair_forest_lane_state_v1(
        &account.try_borrow_data()?,
        &POOL_V1_PAIR_EMPTY_ROOTS,
    )
    .map_err(|_| PoolV1ProgramError::InvalidAccountType)?;
    if lane.master != master.to_bytes() || lane.lane_id != expected_lane || lane.bump != bump {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    Ok(lane)
}

/// Decode the complete canonical lane byte image while treating only the
/// persisted active root/frontier relation as an inductive Pool-owned state
/// invariant. This remains private and is used only by named default-off
/// terminal or deposit audit features. Checkpoint keeps the generic strict
/// codec, and each caller must independently authenticate the retained
/// history root before any CPI or persistence.
#[cfg(any(
    feature = "pair-forest-source-invariant-audit",
    feature = "pair-forest-deposit-invariant-audit"
))]
fn decode_lane_account_from_program_invariant_v1(
    program_id: &Pubkey,
    master: &Pubkey,
    expected_lane: u8,
    account: &AccountInfo<'_>,
    writable: bool,
) -> Result<PoolV1PairForestLaneStateV1, ProgramError> {
    require_program_account(account, program_id, writable)?;
    // Stored canonical bump (G_R1.8); see `decode_lane_account`.
    let stored = stored_lane_bump(account)?;
    let fast = match stored {
        Some(bump) => lane_address_matches(program_id, master, expected_lane, bump, account.key)?,
        None => false,
    };
    let (expected, bump) = if fast {
        (*account.key, stored.unwrap_or_default())
    } else {
        pool_v1_pair_forest_lane_address(program_id, master, expected_lane)?
    };
    if account.is_signer || account.key != &expected {
        return Err(PoolV1ProgramError::InvalidPoolStateAddress.into());
    }
    let data = account.try_borrow_data()?;
    if data.len() != POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES
        || data[..4] != POOL_V1_PAIR_FOREST_LANE_MAGIC
        || data[4] != POOL_V1_PAIR_FOREST_LANE_VERSION
        || usize::from(data[5]) >= POOL_V1_PAIR_FOREST_LANE_COUNT
        || data[6] != POOL_V1_PAIR_FOREST_LANE_COUNT as u8
        || data[7] != POOL_V1_PAIR_TREE_DEPTH as u8
        || data[8..40] != POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING
        || data[73..POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES]
            .iter()
            .any(|byte| *byte != 0)
    {
        return Err(PoolV1ProgramError::InvalidAccountType.into());
    }
    let encoded_master: [u8; 32] = data[40..72].try_into().unwrap();
    if encoded_master == [0u8; 32]
        || encoded_master != master.to_bytes()
        || data[5] != expected_lane
        || data[72] != bump
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    let tree = &data[POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES..];
    if tree[..4] != POOL_V1_TREE_STATE_MAGIC
        || tree[4] != POOL_V1_TREE_STATE_VERSION
        || tree[5] != POOL_V1_PAIR_TREE_DEPTH as u8
        || tree[6] != POOL_V1_TREE_HASH_VERSION
        || tree[7] != POOL_V1_DIGEST_ENCODING_VERSION
    {
        return Err(PoolV1ProgramError::InvalidAccountType.into());
    }
    let next_leaf_index = u64::from_le_bytes(tree[8..16].try_into().unwrap());
    if next_leaf_index > POOL_V1_PAIR_CAPACITY {
        return Err(PoolV1ProgramError::InvalidAccountType.into());
    }
    let root = decode_digest_canonical(tree[16..48].try_into().unwrap())
        .map_err(|_| PoolV1ProgramError::InvalidAccountType)?;
    let mut frontier = [[M31::ZERO; 8]; POOL_V1_PAIR_TREE_DEPTH];
    for (level, node) in frontier.iter_mut().enumerate() {
        let start = 48 + 32 * level;
        *node = decode_digest_canonical(tree[start..start + 32].try_into().unwrap())
            .map_err(|_| PoolV1ProgramError::InvalidAccountType)?;
        if (next_leaf_index >> level) & 1 == 0 && *node != POOL_V1_PAIR_EMPTY_ROOTS[level] {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
    }
    if next_leaf_index == 0 && root != POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH] {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    Ok(PoolV1PairForestLaneStateV1 {
        bump: data[72],
        master: encoded_master,
        lane_id: expected_lane,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index,
            root,
            frontier,
        },
    })
}

/// Byte-exact encoder for an authenticated Pool transition output. It retains
/// all canonical field, capacity, inactive-frontier and genesis checks,
/// omitting only a second root/frontier Poseidon reconstruction already
/// enforced either by the selected verifier relation or by the Pool's checked
/// deposit append construction.
#[cfg(any(
    feature = "pair-forest-source-result-invariant-audit",
    feature = "pair-forest-deposit-invariant-audit"
))]
fn encode_lane_from_authenticated_result_v1(
    lane: &PoolV1PairForestLaneStateV1,
) -> Result<[u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES], ProgramError> {
    if usize::from(lane.lane_id) >= POOL_V1_PAIR_FOREST_LANE_COUNT
        || lane.master == [0u8; 32]
        || lane.tree.next_leaf_index > POOL_V1_PAIR_CAPACITY
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    for (level, node) in lane.tree.frontier.iter().enumerate() {
        if (lane.tree.next_leaf_index >> level) & 1 == 0 && *node != POOL_V1_PAIR_EMPTY_ROOTS[level]
        {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
    }
    if lane.tree.next_leaf_index == 0
        && lane.tree.root != POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH]
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    let mut output = [0u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_LANE_MAGIC);
    output[4] = POOL_V1_PAIR_FOREST_LANE_VERSION;
    output[5] = lane.lane_id;
    output[6] = POOL_V1_PAIR_FOREST_LANE_COUNT as u8;
    output[7] = POOL_V1_PAIR_TREE_DEPTH as u8;
    output[8..40].copy_from_slice(&POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING);
    output[40..72].copy_from_slice(&lane.master);
    output[72] = lane.bump;
    let tree = &mut output[POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES..];
    tree[..4].copy_from_slice(&POOL_V1_TREE_STATE_MAGIC);
    tree[4] = POOL_V1_TREE_STATE_VERSION;
    tree[5] = POOL_V1_PAIR_TREE_DEPTH as u8;
    tree[6] = POOL_V1_TREE_HASH_VERSION;
    tree[7] = POOL_V1_DIGEST_ENCODING_VERSION;
    tree[8..16].copy_from_slice(&lane.tree.next_leaf_index.to_le_bytes());
    tree[16..48].copy_from_slice(&encode_digest_canonical(&lane.tree.root));
    for (level, node) in lane.tree.frontier.iter().enumerate() {
        let start = 48 + 32 * level;
        tree[start..start + 32].copy_from_slice(&encode_digest_canonical(node));
    }
    Ok(output)
}

fn require_alias_free(
    master: &AccountInfo<'_>,
    lanes: &[AccountInfo<'_>],
    checkpoint: &AccountInfo<'_>,
) -> Result<(), ProgramError> {
    if master.key == checkpoint.key {
        return Err(ProgramError::InvalidArgument);
    }
    for (index, lane) in lanes.iter().enumerate() {
        if lane.key == master.key
            || lane.key == checkpoint.key
            || lanes[..index]
                .iter()
                .any(|previous| previous.key == lane.key)
        {
            return Err(ProgramError::InvalidArgument);
        }
    }
    Ok(())
}

#[inline(never)]
fn decode_checkpoint_master_box_v1(
    program_id: &Pubkey,
    master_account: &AccountInfo<'_>,
) -> Result<Box<PoolV1PairForestMasterV1>, ProgramError> {
    Ok(Box::new(decode_master_account(
        program_id,
        master_account,
        true,
    )?))
}

/// Decode the fixed lane snapshot in a separate SBF frame.  Each decoded lane
/// is a large value (root plus the complete depth-20 frontier); keeping the
/// loop in the checkpoint planner made the compiler retain its by-value
/// decode scratch alongside the planner's pure plan and two output images.
/// The returned allocation and the accepted bytes are unchanged.
#[inline(never)]
fn decode_checkpoint_lanes_box_v1(
    program_id: &Pubkey,
    master: &Pubkey,
    lane_accounts: &[AccountInfo<'_>],
) -> Result<Box<[PoolV1PairForestLaneStateV1; POOL_V1_PAIR_FOREST_LANE_COUNT]>, ProgramError> {
    let mut lane_states = Vec::with_capacity(POOL_V1_PAIR_FOREST_LANE_COUNT);
    for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
        lane_states.push(decode_lane_account(
            program_id,
            master,
            lane as u8,
            &lane_accounts[lane],
            false,
        )?);
    }
    lane_states
        .into_boxed_slice()
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)
}

/// Authenticate the exact fixed-order account snapshot and prepare, without
/// mutation, one master update plus one immutable checkpoint image.
pub fn plan_pair_forest_checkpoint_accounts_v1(
    program_id: &Pubkey,
    master_account: &AccountInfo<'_>,
    lane_accounts: &[AccountInfo<'_>],
    checkpoint_account: &AccountInfo<'_>,
) -> Result<PlannedPairForestCheckpointAccountsV1, ProgramError> {
    if lane_accounts.len() != POOL_V1_PAIR_FOREST_LANE_COUNT {
        return Err(if lane_accounts.len() < POOL_V1_PAIR_FOREST_LANE_COUNT {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    }
    require_alias_free(master_account, lane_accounts, checkpoint_account)?;
    let master = decode_checkpoint_master_box_v1(program_id, master_account)?;
    let lane_states =
        decode_checkpoint_lanes_box_v1(program_id, master_account.key, lane_accounts)?;
    let lane_roots = lane_states.each_ref().map(|lane| lane.tree.root);
    let global_root = pool_v1_pair_forest_global_root_v1(&lane_roots);
    let (expected_checkpoint, checkpoint_bump) = pool_v1_pair_forest_checkpoint_address(
        program_id,
        master_account.key,
        master.next_checkpoint_sequence,
    );
    let pure =
        plan_pool_v1_pair_forest_checkpoint_v1(&master, &lane_states, global_root, checkpoint_bump)
            .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    plan_fresh_program_pda(
        checkpoint_account,
        program_id,
        &expected_checkpoint,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
    )?;
    let next_master_image = encode_pool_v1_pair_forest_master_v1(&pure.next_master)
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    let checkpoint_image = encode_pool_v1_pair_forest_checkpoint_v1(&pure.checkpoint)
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    Ok(PlannedPairForestCheckpointAccountsV1 {
        master: *master_account.key,
        checkpoint: expected_checkpoint,
        lane_sequences: pure.checkpoint.lane_sequences,
        next_master_image,
        checkpoint_image,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PairForestDepositPageModeV1 {
    FreshGenesis {
        preparation: FreshPdaPreparationV1,
        bump: u8,
    },
    ExistingSamePage {
        header: RootPageHeaderV1,
    },
    FreshRollover {
        preparation: FreshPdaPreparationV1,
        next_page_number: u64,
        bump: u8,
    },
}

fn account_is_zeroed_program_page(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
) -> Result<bool, ProgramError> {
    if account.owner != program_id || account.data_len() != POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES
    {
        return Ok(false);
    }
    Ok(account.try_borrow_data()?.iter().all(|byte| *byte == 0))
}

fn validate_lane_current_page(
    program_id: &Pubkey,
    lane_account: &AccountInfo<'_>,
    page: &AccountInfo<'_>,
    lane: &PoolV1PairForestLaneStateV1,
    writable: bool,
    bump_hint: Option<u8>,
) -> Result<RootPageHeaderV1, ProgramError> {
    let location = root_history_location(lane.tree.next_leaf_index);
    require_program_account(page, program_id, writable)?;
    if page.is_signer {
        return Err(ProgramError::InvalidAccountData);
    }
    match bump_hint {
        Some(bump) => crate::history::require_root_page_address_with_bump(
            program_id,
            lane_account.key,
            location.page_number,
            bump,
            page,
        )?,
        None => crate::history::require_root_page_address(
            program_id,
            lane_account.key,
            location.page_number,
            page,
        )?,
    }
    let data = page.try_borrow_data()?;
    #[cfg(not(feature = "pair-forest-history-page-invariant-audit"))]
    let header = validate_root_page_bytes(&data, lane_account.key, location.page_number)?;
    #[cfg(feature = "pair-forest-history-page-invariant-audit")]
    let header = crate::history::validate_root_page_bytes_from_program_invariant(
        &data,
        lane_account.key,
        location.page_number,
    )?;
    if header.filled != location.slot + 1
        || read_retained_root(&data, header, lane.tree.next_leaf_index)? != lane.tree.root
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    Ok(header)
}

/// Apply the pair-state module's established binary-carry construction using
/// the pair-leaf empty-root domain. The source root/frontier relation is the
/// one inductive Pool-owned lane invariant; capacity, canonical inactive
/// slots and the retained current root are checked by the deposit caller
/// before this helper's result can be persisted.
#[cfg(feature = "pair-forest-deposit-invariant-audit")]
fn append_pair_leaf_from_program_invariant_v1(
    source: &IncrementalMerkleTreeV1,
    pair_leaf: Digest,
) -> Result<(IncrementalMerkleTreeV1, AppendOneV1), ProgramError> {
    if source.next_leaf_index >= POOL_V1_PAIR_CAPACITY {
        return Err(PoolV1ProgramError::TreeFull.into());
    }
    if pair_leaf.iter().any(|limb| limb.0 >= aspis_core::field::P) {
        return Err(PoolV1ProgramError::NonCanonicalLeaf.into());
    }
    let leaf_index = source.next_leaf_index;
    let mut frontier = source.frontier;
    let mut carry = pair_leaf;
    let mut carry_level = 0usize;
    while carry_level < POOL_V1_PAIR_TREE_DEPTH && (leaf_index >> carry_level) & 1 == 1 {
        carry = pool_v1_tree_parent(&frontier[carry_level], &carry);
        frontier[carry_level] = POOL_V1_PAIR_EMPTY_ROOTS[carry_level];
        carry_level += 1;
    }
    let next_leaf_index = leaf_index
        .checked_add(1)
        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
    let root = if carry_level == POOL_V1_PAIR_TREE_DEPTH {
        carry
    } else {
        frontier[carry_level] = carry;
        let mut node = POOL_V1_PAIR_EMPTY_ROOTS[carry_level];
        for level in carry_level..POOL_V1_PAIR_TREE_DEPTH {
            node = if (next_leaf_index >> level) & 1 == 0 {
                pool_v1_tree_parent(&node, &POOL_V1_PAIR_EMPTY_ROOTS[level])
            } else {
                pool_v1_tree_parent(&frontier[level], &node)
            };
        }
        node
    };
    let next = IncrementalMerkleTreeV1 {
        next_leaf_index,
        root,
        frontier,
    };
    let receipt = AppendOneV1 {
        leaf_index,
        root_sequence: next_leaf_index,
        root,
        history: root_history_location(next_leaf_index),
    };
    Ok((next, receipt))
}

#[inline(never)]
fn prepare_deposit_append_v1(
    lane: &PoolV1PairForestLaneStateV1,
    lane_id: u8,
    pair_leaf: Digest,
) -> Result<
    (
        AppendOneV1,
        Box<[u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES]>,
    ),
    ProgramError,
> {
    #[cfg(not(feature = "pair-forest-deposit-invariant-audit"))]
    let (next_tree, append) = lane
        .tree
        .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
        .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
    #[cfg(feature = "pair-forest-deposit-invariant-audit")]
    let (next_tree, append) = append_pair_leaf_from_program_invariant_v1(&lane.tree, pair_leaf)?;
    let next_lane = Box::new(PoolV1PairForestLaneStateV1 {
        bump: lane.bump,
        master: lane.master,
        lane_id,
        tree: next_tree,
    });
    #[cfg(not(feature = "pair-forest-deposit-invariant-audit"))]
    let next_lane_image = Box::new(
        encode_pool_v1_pair_forest_lane_state_v1(&next_lane, &POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?,
    );
    #[cfg(feature = "pair-forest-deposit-invariant-audit")]
    let next_lane_image = Box::new(encode_lane_from_authenticated_result_v1(&next_lane)?);
    Ok((append, next_lane_image))
}

#[inline(never)]
fn decode_deposit_lane_box_v1(
    program_id: &Pubkey,
    master: &Pubkey,
    lane_id: u8,
    lane_account: &AccountInfo<'_>,
) -> Result<Box<PoolV1PairForestLaneStateV1>, ProgramError> {
    #[cfg(feature = "pair-forest-deposit-invariant-audit")]
    return Ok(Box::new(decode_lane_account_from_program_invariant_v1(
        program_id,
        master,
        lane_id,
        lane_account,
        true,
    )?));

    #[cfg(not(feature = "pair-forest-deposit-invariant-audit"))]
    Ok(Box::new(decode_lane_account(
        program_id,
        master,
        lane_id,
        lane_account,
        true,
    )?))
}

/// Apply one vault-backed public deposit to its deterministic pair-forest
/// lane. The first pair slot is the occupied note commitment and the second
/// slot is the relation's algebraic empty `(occupied = 0, commitment = 0)`.
///
/// Existing-page accounts are
/// `[master, lane, current_page, mint, source, authority, vault, token]`.
/// A fresh genesis page additionally appends `[payer, system]`. Rollover uses
/// `[master, lane, current_page, next_page, mint, source, authority, vault,
/// token, payer, system]`.
pub(crate) fn process_pair_forest_deposit_with_runtime_v1<'info, R: PoolCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    rent: &Rent,
    runtime: &mut R,
) -> ProgramResult {
    let request = decode_pair_forest_deposit_instruction_v1(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let master_account = accounts
        .get(FOREST_DEPOSIT_MASTER_ACCOUNT_INDEX)
        .ok_or(ProgramError::NotEnoughAccountKeys)?;
    let lane_account = accounts
        .get(FOREST_DEPOSIT_LANE_ACCOUNT_INDEX)
        .ok_or(ProgramError::NotEnoughAccountKeys)?;
    let current_page = accounts
        .get(FOREST_DEPOSIT_CURRENT_PAGE_ACCOUNT_INDEX)
        .ok_or(ProgramError::NotEnoughAccountKeys)?;
    let master = decode_terminal_master_box_v1(program_id, master_account)?;
    let commitment = pool_v1_note_commitment(
        &request.owner_key,
        request.amount,
        master.identity.asset_id,
        &request.salt,
    );
    let lane_id = pool_v1_pair_forest_deposit_lane_v1(&commitment)
        .map_err(|_| PoolV1ProgramError::NonCanonicalLeaf)?;
    if master.initialized_lane_mask & (1u8 << lane_id) == 0 {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    let lane = decode_deposit_lane_box_v1(program_id, master_account.key, lane_id, lane_account)?;
    if lane.tree.next_leaf_index >= POOL_V1_PAIR_CAPACITY {
        return Err(PoolV1ProgramError::TreeFull.into());
    }
    let pair_leaf = PoolV1PairLeafWitnessV1::single_output(commitment)
        .and_then(|witness| witness.leaf_digest())
        .map_err(|_| PoolV1ProgramError::NonCanonicalLeaf)?;
    let (append, next_lane_image) = prepare_deposit_append_v1(&lane, lane_id, pair_leaf)?;

    let current_location = root_history_location(lane.tree.next_leaf_index);
    let next_location = root_history_location(append.root_sequence);
    let fresh_genesis = lane.tree.next_leaf_index == 0
        && ((current_page.owner == &solana_sdk_ids::system_program::id()
            && current_page.data_is_empty())
            || account_is_zeroed_program_page(current_page, program_id)?);
    let (mode, token_start, expected_accounts) = if fresh_genesis {
        let (expected, bump) = pool_v1_root_page_address(program_id, lane_account.key, 0);
        let preparation = plan_fresh_program_pda(
            current_page,
            program_id,
            &expected,
            POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        )?;
        (
            PairForestDepositPageModeV1::FreshGenesis { preparation, bump },
            3,
            FOREST_DEPOSIT_GENESIS_PAGE_ACCOUNT_COUNT,
        )
    } else if next_location.page_number == current_location.page_number {
        let header =
            validate_lane_current_page(program_id, lane_account, current_page, &lane, true, None)?;
        (
            PairForestDepositPageModeV1::ExistingSamePage { header },
            3,
            FOREST_DEPOSIT_SAME_PAGE_ACCOUNT_COUNT,
        )
    } else {
        let current_header =
            validate_lane_current_page(program_id, lane_account, current_page, &lane, false, None)?;
        if usize::from(current_header.filled) != POOL_V1_ROOT_HISTORY_CAPACITY {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        let next_page = accounts.get(3).ok_or(ProgramError::NotEnoughAccountKeys)?;
        let (expected, bump) =
            pool_v1_root_page_address(program_id, lane_account.key, next_location.page_number);
        let preparation = plan_fresh_program_pda(
            next_page,
            program_id,
            &expected,
            POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
        )?;
        (
            PairForestDepositPageModeV1::FreshRollover {
                preparation,
                next_page_number: next_location.page_number,
                bump,
            },
            4,
            FOREST_DEPOSIT_ROLLOVER_ACCOUNT_COUNT,
        )
    };

    require_exact_account_count(accounts, expected_accounts)?;
    require_unique_accounts(accounts)?;
    let token_accounts = &accounts[token_start..token_start + 5];
    require_token_program_account(&token_accounts[4])?;
    let transfer_plan = plan_legacy_deposit_transfer_from_identity_v1(
        program_id,
        master_account.key,
        &master.identity,
        token_accounts,
        request.amount,
    )?;
    let transfer_infos = exact_transfer_account_infos_v1(token_accounts)?;

    let writable_page = match mode {
        PairForestDepositPageModeV1::FreshGenesis { preparation, bump } => {
            let payer = &accounts[8];
            let system_program = &accounts[9];
            require_payer_and_system_program(payer, system_program)?;
            if preparation == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
                let page_number = 0u64.to_le_bytes();
                let bump = [bump];
                let seeds: &[&[u8]] = &[
                    POOL_V1_ROOT_HISTORY_PAGE_SEED,
                    lane_account.key.as_ref(),
                    &page_number,
                    &bump,
                ];
                create_or_allocate_pda(
                    runtime,
                    payer,
                    current_page,
                    system_program,
                    POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
                    program_id,
                    seeds,
                )?;
            }
            require_program_owned_zeroed(
                current_page,
                program_id,
                POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
                rent,
            )?;
            current_page
        }
        PairForestDepositPageModeV1::ExistingSamePage { .. } => current_page,
        PairForestDepositPageModeV1::FreshRollover {
            preparation,
            next_page_number,
            bump,
            ..
        } => {
            let next_page = &accounts[3];
            let payer = &accounts[9];
            let system_program = &accounts[10];
            require_payer_and_system_program(payer, system_program)?;
            if preparation == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
                let page_number = next_page_number.to_le_bytes();
                let bump = [bump];
                let seeds: &[&[u8]] = &[
                    POOL_V1_ROOT_HISTORY_PAGE_SEED,
                    lane_account.key.as_ref(),
                    &page_number,
                    &bump,
                ];
                create_or_allocate_pda(
                    runtime,
                    payer,
                    next_page,
                    system_program,
                    POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
                    program_id,
                    seeds,
                )?;
            }
            require_program_owned_zeroed(
                next_page,
                program_id,
                POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
                rent,
            )?;
            next_page
        }
    };

    // Acquire every Pool-owned mutable borrow before the token CPI. A failed
    // CPI or post-CPI balance check therefore leaves writes to Solana's outer
    // transaction rollback boundary, with no partial Pool persistence.
    let mut lane_data = lane_account.try_borrow_mut_data()?;
    let mut page_data = writable_page.try_borrow_mut_data()?;
    runtime.invoke(&transfer_plan.instruction, &transfer_infos)?;
    validate_exact_deposit_delta_v1(token_accounts, &transfer_plan)?;

    lane_data.copy_from_slice(next_lane_image.as_ref());
    match mode {
        PairForestDepositPageModeV1::FreshGenesis { .. } => write_new_page_unchecked(
            &mut page_data,
            lane_account.key,
            0,
            0,
            &[lane.tree.root, append.root],
        ),
        PairForestDepositPageModeV1::ExistingSamePage { header } => {
            append_roots_unchecked(&mut page_data, header, &[append.root]);
        }
        PairForestDepositPageModeV1::FreshRollover {
            next_page_number, ..
        } => write_new_page_unchecked(
            &mut page_data,
            lane_account.key,
            next_page_number,
            append.root_sequence,
            &[append.root],
        ),
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum PairForestSpendPageV1 {
    Genesis,
    SamePage(RootPageHeaderV1),
    Rollover { next_index: usize, page_number: u64 },
}

#[derive(Clone, Copy)]
struct PairForestSpendLayoutV1 {
    page: PairForestSpendPageV1,
    marker_index: usize,
    payer_index: usize,
    system_program_index: usize,
    registry_start: usize,
    verifier_index: usize,
    proof_index: usize,
    verifier_checkpoint_index: Option<usize>,
    token_start: usize,
}

fn plan_pair_forest_spend_layout_v1(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    lane: &PoolV1PairForestLaneStateV1,
    withdrawal: bool,
    hints: PoolV1PairForestTerminalBumpHintsV1,
) -> Result<PairForestSpendLayoutV1, ProgramError> {
    if lane.tree.next_leaf_index >= POOL_V1_PAIR_CAPACITY {
        return Err(PoolV1ProgramError::TreeFull.into());
    }
    let lane_account = accounts.get(2).ok_or(ProgramError::NotEnoughAccountKeys)?;
    let current = accounts.get(3).ok_or(ProgramError::NotEnoughAccountKeys)?;
    let current_location = root_history_location(lane.tree.next_leaf_index);
    let next_location = root_history_location(lane.tree.next_leaf_index + 1);
    let (page, cursor) = if lane.tree.next_leaf_index == 0
        && account_is_zeroed_program_page(current, program_id)?
    {
        crate::history::require_root_page_address_with_bump(
            program_id,
            lane_account.key,
            0,
            hints.current_page,
            current,
        )?;
        require_program_account(current, program_id, true)?;
        (PairForestSpendPageV1::Genesis, 4)
    } else if current_location.page_number == next_location.page_number {
        let header = validate_lane_current_page(
            program_id,
            lane_account,
            current,
            lane,
            true,
            Some(hints.current_page),
        )?;
        (PairForestSpendPageV1::SamePage(header), 4)
    } else {
        let header = validate_lane_current_page(
            program_id,
            lane_account,
            current,
            lane,
            false,
            Some(hints.current_page),
        )?;
        if usize::from(header.filled) != POOL_V1_ROOT_HISTORY_CAPACITY {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
        let next_index = 4;
        let next = accounts
            .get(next_index)
            .ok_or(ProgramError::NotEnoughAccountKeys)?;
        crate::history::require_root_page_address_with_bump(
            program_id,
            lane_account.key,
            next_location.page_number,
            hints.next_page,
            next,
        )?;
        if !account_is_zeroed_program_page(next, program_id)? || !next.is_writable {
            return Err(PoolV1ProgramError::InvalidFreshAccount.into());
        }
        (
            PairForestSpendPageV1::Rollover {
                next_index,
                page_number: next_location.page_number,
            },
            5,
        )
    };
    if cursor == 4 && hints.next_page != 0 {
        // Canonical encoding: an unused hint byte is zero.
        return Err(ProgramError::InvalidInstructionData);
    }
    let marker_index = cursor;
    let payer_index = cursor + 1;
    let system_program_index = cursor + 2;
    let registry_start = cursor + 3;
    let verifier_index = cursor + 5;
    let proof_index = cursor + 6;
    let token_start: usize = cursor + 7;
    let expected = token_start
        .checked_add(if withdrawal { 5 } else { 0 })
        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
    // Append the R1 verifier checkpoint after the complete legacy layout,
    // including withdrawal custody accounts. Proof and token indices stay fixed.
    let verifier_checkpoint_index = cfg!(feature = "r1-split-checkpoint").then_some(expected);
    let expected = expected + usize::from(verifier_checkpoint_index.is_some());
    require_exact_account_count(accounts, expected)?;
    require_unique_accounts(accounts)?;
    Ok(PairForestSpendLayoutV1 {
        page,
        marker_index,
        payer_index,
        system_program_index,
        registry_start,
        verifier_index,
        proof_index,
        verifier_checkpoint_index,
        token_start,
    })
}

fn validate_pair_forest_request_accounts_v1(
    program_id: &Pubkey,
    master_account: &AccountInfo<'_>,
    checkpoint_account: &AccountInfo<'_>,
    lane_account: &AccountInfo<'_>,
    master: &PoolV1PairForestMasterV1,
    checkpoint: &PoolV1PairForestCheckpointV1,
    lane: &PoolV1PairForestLaneStateV1,
    request: &PoolV1PairForestTerminalRequestV1,
) -> ProgramResult {
    if request.pool_program != program_id.to_bytes() {
        return Err(PoolV1ProgramError::VerifierDispatchIdentityMismatch.into());
    }
    let (pool, deployment, anchor_sequence, anchor_root, asset_id, destination) =
        match request.public {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => (
                public.pool,
                public.deployment_domain,
                public.anchor_sequence,
                public.anchor_root,
                public.asset_id,
                [0u8; 32],
            ),
            PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => (
                public.pool,
                public.deployment_domain,
                public.anchor_sequence,
                public.anchor_root,
                public.asset_id,
                public.destination_token_account,
            ),
        };
    let output_lane =
        aspis_statement::pool_v1::pool_v1_pair_forest_output_lane_v1(request.public.nullifier())
            .map_err(|_| PoolV1ProgramError::NonCanonicalLeaf)?;
    if pool != master_account.key.to_bytes()
        || master.identity.pool != pool
        || deployment != master.identity.deployment_domain
        || asset_id != master.identity.asset_id
        || checkpoint_account.key.to_bytes() == [0u8; 32]
        || checkpoint.master != pool
        || checkpoint.deployment_domain != deployment
        || checkpoint.checkpoint_sequence != anchor_sequence
        || checkpoint.global_root != anchor_root
        || !lane_address_matches(
            program_id,
            master_account.key,
            output_lane,
            lane.bump,
            lane_account.key,
        )?
        || lane.master != pool
        || lane.lane_id != output_lane
        || master.initialized_lane_mask & (1u8 << output_lane) == 0
        || (request.public.transition_kind()
            == aspis_statement::pool_v1::PoolV1TransitionKind::Withdrawal
            && destination == [0u8; 32])
    {
        return Err(PoolV1ProgramError::VerifierDispatchIdentityMismatch.into());
    }
    Ok(())
}

fn next_pair_forest_lane_v1(
    lane: &PoolV1PairForestLaneStateV1,
    result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
) -> Result<PoolV1PairForestLaneStateV1, ProgramError> {
    let afterstate = result.verified_afterstate;
    if lane.tree.next_leaf_index.checked_add(1) != Some(afterstate.next_pair_index) {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    for (level, node) in afterstate.next_frontier.iter().enumerate() {
        if (afterstate.next_pair_index >> level) & 1 == 0
            && *node != POOL_V1_PAIR_EMPTY_ROOTS[level]
        {
            return Err(PoolV1ProgramError::StateHistoryMismatch.into());
        }
    }
    Ok(PoolV1PairForestLaneStateV1 {
        master: lane.master,
        bump: lane.bump,
        lane_id: lane.lane_id,
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index: afterstate.next_pair_index,
            root: afterstate.next_root,
            frontier: afterstate.next_frontier,
        },
    })
}

#[inline(never)]
fn decode_terminal_request_box_v1(
    instruction_data: &[u8],
) -> Result<Box<PoolV1PairForestTerminalRequestV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_forest_terminal_request_v1(instruction_data)
            .map_err(|_| ProgramError::InvalidInstructionData)?,
    ))
}

#[inline(never)]
fn decode_terminal_master_box_v1(
    program_id: &Pubkey,
    master_account: &AccountInfo<'_>,
) -> Result<Box<PoolV1PairForestMasterV1>, ProgramError> {
    Ok(Box::new(decode_master_account(
        program_id,
        master_account,
        false,
    )?))
}

#[inline(never)]
fn decode_terminal_checkpoint_box_v1(
    program_id: &Pubkey,
    master: &Pubkey,
    checkpoint_account: &AccountInfo<'_>,
) -> Result<Box<PoolV1PairForestCheckpointV1>, ProgramError> {
    Ok(Box::new(decode_retained_pair_forest_checkpoint_account_v1(
        program_id,
        master,
        checkpoint_account,
    )?))
}

#[inline(never)]
fn decode_terminal_lane_box_v1(
    program_id: &Pubkey,
    master: &Pubkey,
    lane_id: u8,
    lane_account: &AccountInfo<'_>,
) -> Result<Box<PoolV1PairForestLaneStateV1>, ProgramError> {
    #[cfg(feature = "pair-forest-source-invariant-audit")]
    return Ok(Box::new(decode_lane_account_from_program_invariant_v1(
        program_id,
        master,
        lane_id,
        lane_account,
        true,
    )?));

    #[cfg(not(feature = "pair-forest-source-invariant-audit"))]
    Ok(Box::new(decode_lane_account(
        program_id,
        master,
        lane_id,
        lane_account,
        true,
    )?))
}

#[inline(never)]
fn terminal_common_box_v1(
    master_account: &Pubkey,
    checkpoint_account: &Pubkey,
    lane_account: &Pubkey,
    master: &PoolV1PairForestMasterV1,
    checkpoint: &PoolV1PairForestCheckpointV1,
    lane: &PoolV1PairForestLaneStateV1,
    output_lane: u8,
    result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
) -> Box<PoolV1PairForestTerminalCommonV1> {
    Box::new(PoolV1PairForestTerminalCommonV1 {
        master_account: master_account.to_bytes(),
        checkpoint_account: checkpoint_account.to_bytes(),
        selected_lane_account: lane_account.to_bytes(),
        output_lane,
        checkpoint_sequence: checkpoint.checkpoint_sequence,
        historical_global_anchor: checkpoint.global_root,
        lane_transition: aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1 {
            live_snapshot: aspis_statement::pool_v1::PoolV1PairLiveSnapshotV1 {
                pool: master_account.to_bytes(),
                deployment_domain: master.identity.deployment_domain,
                sequence: lane.tree.next_leaf_index,
                next_pair_index: lane.tree.next_leaf_index,
                current_root: lane.tree.root,
                frontier: lane.tree.frontier,
            },
            candidate_afterstate: result.verified_afterstate,
        },
    })
}

#[inline(never)]
fn transfer_terminal_statement_box_v1(
    common: Box<PoolV1PairForestTerminalCommonV1>,
    public: aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1,
) -> Box<PoolV1PairForestTerminalStatementV1> {
    Box::new(PoolV1PairForestTerminalStatementV1::PrivateTransfer {
        common: *common,
        public,
    })
}

#[inline(never)]
fn withdrawal_terminal_statement_box_v1(
    common: Box<PoolV1PairForestTerminalCommonV1>,
    public: aspis_statement::pool_v1::PoolV1WithdrawalPublicV1,
) -> Box<PoolV1PairForestTerminalStatementV1> {
    Box::new(PoolV1PairForestTerminalStatementV1::Withdrawal {
        common: *common,
        public,
    })
}

#[inline(never)]
fn validate_authenticated_terminal_result_v1(
    master_account: &Pubkey,
    checkpoint_account: &Pubkey,
    lane_account: &Pubkey,
    master: &PoolV1PairForestMasterV1,
    checkpoint: &PoolV1PairForestCheckpointV1,
    lane: &PoolV1PairForestLaneStateV1,
    output_lane: u8,
    request: &PoolV1PairForestTerminalRequestV1,
    result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
) -> ProgramResult {
    let common = terminal_common_box_v1(
        master_account,
        checkpoint_account,
        lane_account,
        master,
        checkpoint,
        lane,
        output_lane,
        result,
    );
    let statement = match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => {
            transfer_terminal_statement_box_v1(common, public)
        }
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
            withdrawal_terminal_statement_box_v1(common, public)
        }
    };
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1(&statement, result)
        .map_err(|_| PoolV1ProgramError::InvalidVerifierReturnData.into())
}

/// Exact field-wise form of the same result/statement binding after the Pool
/// has authenticated the request, master, checkpoint, lane, verifier release
/// and canonical ASR8 return bytes. It avoids allocating and validating a
/// second ASF8 object while retaining every equality used by
/// `validate_pool_v1_pair_forest_terminal_result_against_statement_v1`.
#[cfg(feature = "pair-forest-direct-result-audit")]
#[inline(never)]
fn validate_pair_forest_terminal_result_direct_v1(
    request: &PoolV1PairForestTerminalRequestV1,
    master_account: &Pubkey,
    lane_account: &Pubkey,
    output_lane: u8,
    lane: &PoolV1PairForestLaneStateV1,
    result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
) -> ProgramResult {
    if result.transition_kind != request.public.transition_kind()
        || result.master_account != master_account.to_bytes()
        || result.selected_lane_account != lane_account.to_bytes()
        || result.output_lane != output_lane
        || result.nullifier != *request.public.nullifier()
        || lane.tree.next_leaf_index.checked_add(1)
            != Some(result.verified_afterstate.next_pair_index)
    {
        return Err(PoolV1ProgramError::InvalidVerifierReturnData.into());
    }
    Ok(())
}

#[inline(never)]
fn next_lane_image_box_v1(
    lane: &PoolV1PairForestLaneStateV1,
    result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
) -> Result<Box<[u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES]>, ProgramError> {
    let next_lane = Box::new(next_pair_forest_lane_v1(lane, result)?);
    #[cfg(feature = "pair-forest-source-result-invariant-audit")]
    let image = Box::new(encode_lane_from_authenticated_result_v1(&next_lane)?);
    #[cfg(not(feature = "pair-forest-source-result-invariant-audit"))]
    let image = Box::new(
        encode_pool_v1_pair_forest_lane_state_v1(&next_lane, &POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?,
    );
    Ok(image)
}

#[inline(never)]
fn terminal_result_bytes_box_v1(
    result: &aspis_statement::pool_v1::PoolV1PairForestTerminalResultV1,
) -> Result<Box<[u8; POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES]>, ProgramError> {
    Ok(Box::new(
        encode_pool_v1_pair_forest_terminal_result_v1(result)
            .map_err(|_| PoolV1ProgramError::InvalidVerifierReturnData)?,
    ))
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn process_pair_forest_terminal_with_verifier_v1<'info, R, V, S>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    current_slot: u64,
    rent: &Rent,
    runtime: &mut R,
    verify: V,
    set_return_data: S,
) -> ProgramResult
where
    R: PoolCpiRuntimeV1,
    V: FnOnce(
        &Pubkey,
        &AccountInfo<'info>,
        &AccountInfo<'info>,
        &AccountInfo<'info>,
        &aspis_statement::pool_v1::VerifierPolicyV1,
        &[AccountInfo<'info>],
        &AccountInfo<'info>,
        &AccountInfo<'info>,
        Option<&AccountInfo<'info>>,
        &PoolV1PairForestTerminalRequestV1,
        u64,
    ) -> Result<AuthenticatedPairForestResultV1, ProgramError>,
    S: FnOnce(&[u8]),
{
    let (request_bytes, hints) = split_pair_forest_terminal_bump_hints_v1(instruction_data)?;
    let request = decode_terminal_request_box_v1(request_bytes)?;
    let master_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let checkpoint_account = accounts.get(1).ok_or(ProgramError::NotEnoughAccountKeys)?;
    let lane_account = accounts.get(2).ok_or(ProgramError::NotEnoughAccountKeys)?;
    let master = decode_terminal_master_box_v1(program_id, master_account)?;
    let checkpoint =
        decode_terminal_checkpoint_box_v1(program_id, master_account.key, checkpoint_account)?;
    let output_lane =
        aspis_statement::pool_v1::pool_v1_pair_forest_output_lane_v1(request.public.nullifier())
            .map_err(|_| PoolV1ProgramError::NonCanonicalLeaf)?;
    let lane =
        decode_terminal_lane_box_v1(program_id, master_account.key, output_lane, lane_account)?;
    validate_pair_forest_request_accounts_v1(
        program_id,
        master_account,
        checkpoint_account,
        lane_account,
        &master,
        &checkpoint,
        &lane,
        &request,
    )?;
    let withdrawal = matches!(
        request.public,
        PoolV1PairForestTerminalPaymentV1::Withdrawal(_)
    );
    if !withdrawal && (hints.vault_authority != 0 || hints.vault_token_account != 0) {
        // Canonical encoding: a transfer carries no custody hints.
        return Err(ProgramError::InvalidInstructionData);
    }
    let layout = plan_pair_forest_spend_layout_v1(program_id, accounts, &lane, withdrawal, hints)?;
    let payer = &accounts[layout.payer_index];
    let system_program_account = &accounts[layout.system_program_index];
    require_payer_and_system_program(payer, system_program_account)?;

    let marker = &accounts[layout.marker_index];
    let marker_payload = PoolV1NullifierMarkerV1 {
        transition_kind: request.public.transition_kind(),
        pool: master_account.key.to_bytes(),
        deployment_domain: master.identity.deployment_domain,
        nullifier: *request.public.nullifier(),
        retained_anchor_sequence: checkpoint.checkpoint_sequence,
        retained_anchor_root: checkpoint.global_root,
        verifier_profile: request.verifier_profile,
        verifier_release: request.verifier_release,
    };
    // B1: one seed hash and one address hash; no bump search.
    let planned_marker =
        plan_pair_forest_nullifier_marker_consumption_v1(program_id, marker, marker_payload)?;

    let withdrawal_plan =
        if let PoolV1PairForestTerminalPaymentV1::Withdrawal(public) = request.public {
            let token_accounts = &accounts[layout.token_start..layout.token_start + 5];
            require_token_program_account(&token_accounts[4])?;
            Some(plan_legacy_withdrawal_transfer_from_identity_v1(
                program_id,
                master_account.key,
                &master.identity,
                token_accounts,
                &Pubkey::new_from_array(public.destination_token_account),
                public.amount,
                Some(hints.vault()),
            )?)
        } else {
            None
        };

    // Reserve the exact nullifier marker immediately before verifier CPI.
    // Solana rolls this System CPI back with every later write if
    // verification or settlement fails. The master PDA (authenticated by its
    // stored bump) is the `create_with_seed` base and signs; the re-check
    // authenticates the resulting owner, size, zero image and rent reserve.
    let master_bump = [master.bump];
    let master_signer_seeds: &[&[u8]] = &[
        POOL_V1_PAIR_FOREST_MASTER_SEED,
        &master.identity.asset_mint,
        &master_bump,
    ];
    let ready_marker = create_pair_forest_nullifier_marker_if_needed_v1(
        runtime,
        program_id,
        master_account,
        master_signer_seeds,
        marker,
        payer,
        system_program_account,
        planned_marker,
        rent,
    )?;

    let authenticated = verify(
        program_id,
        master_account,
        checkpoint_account,
        lane_account,
        &master.verifier_policy,
        &accounts[layout.registry_start..layout.registry_start + 2],
        &accounts[layout.verifier_index],
        &accounts[layout.proof_index],
        layout
            .verifier_checkpoint_index
            .map(|index| &accounts[index]),
        &request,
        current_slot,
    )?;
    let result = authenticated.value();
    #[cfg(not(feature = "pair-forest-direct-result-audit"))]
    validate_authenticated_terminal_result_v1(
        master_account.key,
        checkpoint_account.key,
        lane_account.key,
        &master,
        &checkpoint,
        &lane,
        output_lane,
        &request,
        result,
    )?;
    #[cfg(feature = "pair-forest-direct-result-audit")]
    validate_pair_forest_terminal_result_direct_v1(
        &request,
        master_account.key,
        lane_account.key,
        output_lane,
        &lane,
        result,
    )?;
    let next_lane_image = next_lane_image_box_v1(&lane, result)?;
    #[cfg(not(feature = "pair-forest-direct-result-audit"))]
    let result_bytes = terminal_result_bytes_box_v1(result)?;
    #[cfg(feature = "pair-forest-direct-result-audit")]
    let result_bytes = authenticated.exact_bytes();

    let writable_page = match layout.page {
        PairForestSpendPageV1::Genesis | PairForestSpendPageV1::SamePage(_) => &accounts[3],
        PairForestSpendPageV1::Rollover { next_index, .. } => &accounts[next_index],
    };
    let mut lane_data = lane_account.try_borrow_mut_data()?;
    let mut page_data = writable_page.try_borrow_mut_data()?;
    let mut marker_data = marker.try_borrow_mut_data()?;
    if let Some(plan) = withdrawal_plan {
        let token_accounts = &accounts[layout.token_start..layout.token_start + 5];
        let infos = exact_withdrawal_transfer_account_infos_v1(token_accounts)?;
        let bump = [plan.authority_bump];
        let seeds: &[&[u8]] = &[
            POOL_V1_VAULT_AUTHORITY_SEED,
            master_account.key.as_ref(),
            &bump,
        ];
        runtime.invoke_signed(&plan.instruction, &infos, &[seeds])?;
        validate_exact_withdrawal_delta_v1(token_accounts, &plan)?;
    }

    lane_data.copy_from_slice(next_lane_image.as_ref());
    match layout.page {
        PairForestSpendPageV1::Genesis => write_new_page_unchecked(
            &mut page_data,
            lane_account.key,
            0,
            0,
            &[lane.tree.root, result.verified_afterstate.next_root],
        ),
        PairForestSpendPageV1::SamePage(header) => append_roots_unchecked(
            &mut page_data,
            header,
            &[result.verified_afterstate.next_root],
        ),
        PairForestSpendPageV1::Rollover { page_number, .. } => write_new_page_unchecked(
            &mut page_data,
            lane_account.key,
            page_number,
            result.verified_afterstate.next_pair_index,
            &[result.verified_afterstate.next_root],
        ),
    }
    marker_data.copy_from_slice(&ready_marker.encoded_marker());
    set_return_data(result_bytes.as_ref());
    Ok(())
}

pub(crate) fn process_pair_forest_terminal_v1<'info, R: PoolCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    current_slot: u64,
    rent: &Rent,
    runtime: &mut R,
) -> ProgramResult {
    process_pair_forest_terminal_with_verifier_v1(
        program_id,
        accounts,
        instruction_data,
        current_slot,
        rent,
        runtime,
        dispatch_pair_forest_terminal_readonly_v1,
        solana_program::program::set_return_data,
    )
}

/// Audit-only Pool top-level ASF8 route. The supplied statement is decoded
/// canonically to recover the compact registry/payment request, while the
/// exact original 1,880 bytes are forwarded to the selected verifier. The
/// selected verifier independently authenticates and reconstructs ASF8 before
/// running the same proof and returning the same exact ASR8 settlement token.
#[cfg(feature = "pair-forest-full-asf8-audit")]
#[inline(never)]
fn decode_terminal_statement_box_v1(
    instruction_data: &[u8],
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_forest_terminal_statement_v1(instruction_data)
            .map_err(|_| ProgramError::InvalidInstructionData)?,
    ))
}

#[cfg(feature = "pair-forest-full-asf8-audit")]
#[inline(never)]
fn compact_request_from_terminal_statement_box_v1(
    program_id: &Pubkey,
    statement: &PoolV1PairForestTerminalStatementV1,
) -> Result<
    Box<[u8; aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES]>,
    ProgramError,
> {
    let public = match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(*public)
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => {
            PoolV1PairForestTerminalPaymentV1::Withdrawal(*public)
        }
    };
    let request = PoolV1PairForestTerminalRequestV1 {
        verifier_profile: aspis_statement::pool_v1::V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING,
        verifier_release: aspis_statement::pool_v1::V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
        pool_program: program_id.to_bytes(),
        public,
    };
    Ok(Box::new(
        encode_pool_v1_pair_forest_terminal_request_v1(&request)
            .map_err(|_| ProgramError::InvalidInstructionData)?,
    ))
}

#[cfg(feature = "pair-forest-full-asf8-audit")]
#[inline(never)]
pub(crate) fn process_pair_forest_terminal_full_asf8_v1<'info, R: PoolCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    current_slot: u64,
    rent: &Rent,
    runtime: &mut R,
) -> ProgramResult {
    // `statement || hints`: the verifier receives the exact statement only.
    let (statement_bytes, hints) = split_pair_forest_terminal_bump_hints_v1(instruction_data)?;
    let statement = decode_terminal_statement_box_v1(statement_bytes)?;
    let compact = compact_request_from_terminal_statement_box_v1(program_id, &statement)?;
    let compact_with_hints = encode_pair_forest_terminal_instruction_data_v1(compact.as_ref(), hints);
    process_pair_forest_terminal_with_verifier_v1(
        program_id,
        accounts,
        &compact_with_hints,
        current_slot,
        rent,
        runtime,
        |pool_program,
         master,
         checkpoint,
         lane,
         policy,
         registry_accounts,
         verifier_program,
         proof,
         verifier_checkpoint,
         request,
         slot| {
            crate::pair_forest_dispatch::dispatch_pair_forest_terminal_full_asf8_readonly_v1(
                pool_program,
                master,
                checkpoint,
                lane,
                policy,
                registry_accounts,
                verifier_program,
                proof,
                verifier_checkpoint,
                request,
                slot,
                statement_bytes,
            )
        },
        solana_program::program::set_return_data,
    )
}

#[inline(never)]
fn decode_forest_initialization_box_v1(
    instruction_data: &[u8],
) -> Result<Box<PoolInitializationV1>, ProgramError> {
    Ok(Box::new(decode_pair_forest_initialize_instruction_v1(
        instruction_data,
    )?))
}

#[inline(never)]
fn forest_master_image_box_v1(
    expected_master: &Pubkey,
    initialization: &PoolInitializationV1,
    master_bump: u8,
) -> Result<Box<[u8; POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES]>, ProgramError> {
    let master_state = Box::new(PoolV1PairForestMasterV1 {
        bump: master_bump,
        identity: PoolIdentityV1 {
            pool: expected_master.to_bytes(),
            asset_mint: initialization.asset_mint,
            token_program: initialization.token_program,
            asset_id: initialization.asset_id,
            deployment_domain: initialization.deployment_domain,
        },
        verifier_policy: initialization.verifier_policy,
        initialized_lane_mask: aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
        has_checkpoint: false,
        next_checkpoint_sequence: 0,
        last_checkpoint_lane_sequences: [0u64; POOL_V1_PAIR_FOREST_LANE_COUNT],
    });
    Ok(Box::new(
        encode_pool_v1_pair_forest_master_v1(&master_state)
            .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?,
    ))
}

#[inline(never)]
fn genesis_lane_image_box_v1(
    expected_master: &Pubkey,
    lane_id: u8,
    lane_bump: u8,
) -> Result<Box<[u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES]>, ProgramError> {
    let lane = Box::new(genesis_lane_state(expected_master, lane_id, lane_bump));
    Ok(Box::new(
        encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS)
            .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?,
    ))
}

/// Initialize
/// `[master, lane_0, ..., lane_7, mint, vault, token_program, payer,
/// system_program]`.
/// Every program account is either a fresh System account at its canonical PDA
/// or an exactly sized, zeroed, precreated Pool-owned account.
pub(crate) fn process_pair_forest_initialize_with_runtime_v1<'info, R: PoolCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    rent: &Rent,
    runtime: &mut R,
) -> ProgramResult {
    require_exact_account_count(accounts, POOL_V1_PAIR_FOREST_INITIALIZE_ACCOUNT_COUNT)?;
    require_unique_accounts(accounts)?;
    let initialization = decode_forest_initialization_box_v1(instruction_data)?;
    let master = &accounts[FOREST_MASTER_ACCOUNT_INDEX];
    let lanes = &accounts[FOREST_FIRST_LANE_ACCOUNT_INDEX
        ..FOREST_FIRST_LANE_ACCOUNT_INDEX + POOL_V1_PAIR_FOREST_LANE_COUNT];
    let mint = &accounts[FOREST_MINT_OR_CHECKPOINT_ACCOUNT_INDEX];
    let vault = &accounts[FOREST_INIT_VAULT_ACCOUNT_INDEX];
    let token_program = &accounts[FOREST_INIT_TOKEN_PROGRAM_ACCOUNT_INDEX];
    let payer = &accounts[FOREST_INIT_PAYER_ACCOUNT_INDEX];
    let system_program_account = &accounts[FOREST_INIT_SYSTEM_ACCOUNT_INDEX];
    require_payer_and_system_program(payer, system_program_account)?;
    require_token_program_account(token_program)?;
    require_forest_mint_account(&initialization, mint)?;

    let (expected_master, master_bump) = pool_v1_pair_forest_master_address(program_id, mint.key);
    let master_preparation = plan_fresh_program_pda(
        master,
        program_id,
        &expected_master,
        POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
    )?;
    let vault_preparation =
        plan_vault_initialization(program_id, &expected_master, mint.key, vault)?;
    let mut lane_preparations =
        [FreshPdaPreparationV1::ProgramOwnedZeroed; POOL_V1_PAIR_FOREST_LANE_COUNT];
    let mut lane_bumps = [0u8; POOL_V1_PAIR_FOREST_LANE_COUNT];
    for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
        let (expected_lane, bump) =
            pool_v1_pair_forest_lane_address(program_id, &expected_master, lane as u8)?;
        lane_preparations[lane] = plan_fresh_program_pda(
            &lanes[lane],
            program_id,
            &expected_lane,
            aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
        )?;
        lane_bumps[lane] = bump;
    }

    // Freeze every program-owned output image before the first CPI.
    let master_image = forest_master_image_box_v1(&expected_master, &initialization, master_bump)?;
    let mut lane_images = Vec::with_capacity(POOL_V1_PAIR_FOREST_LANE_COUNT);
    for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
        lane_images.push(genesis_lane_image_box_v1(
            &expected_master,
            lane as u8,
            lane_bumps[lane],
        )?);
    }

    if master_preparation == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
        let bump = [master_bump];
        let seeds: &[&[u8]] = &[POOL_V1_PAIR_FOREST_MASTER_SEED, mint.key.as_ref(), &bump];
        create_or_allocate_pda(
            runtime,
            payer,
            master,
            system_program_account,
            POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
            program_id,
            seeds,
        )?;
    }
    for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
        if lane_preparations[lane] == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
            let lane_id = [lane as u8];
            let bump = [lane_bumps[lane]];
            let seeds: &[&[u8]] = &[
                POOL_V1_PAIR_FOREST_LANE_SEED,
                expected_master.as_ref(),
                &lane_id,
                &bump,
            ];
            create_or_allocate_pda(
                runtime,
                payer,
                &lanes[lane],
                system_program_account,
                aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
                program_id,
                seeds,
            )?;
        }
    }
    initialize_vault_account(
        runtime,
        program_id,
        &expected_master,
        mint,
        vault,
        token_program,
        payer,
        system_program_account,
        vault_preparation,
    )?;

    require_program_owned_zeroed(
        master,
        program_id,
        POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES,
        rent,
    )?;
    for lane in lanes {
        require_program_owned_zeroed(
            lane,
            program_id,
            aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
            rent,
        )?;
    }

    // Acquire every mutable borrow before the first write. Runtime rollback
    // remains the outer atomicity boundary for preceding System CPIs.
    let mut master_data = master.try_borrow_mut_data()?;
    let mut lane_data = Vec::with_capacity(POOL_V1_PAIR_FOREST_LANE_COUNT);
    for lane in lanes {
        lane_data.push(lane.try_borrow_mut_data()?);
    }
    master_data.copy_from_slice(master_image.as_ref());
    for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
        lane_data[lane].copy_from_slice(lane_images[lane].as_ref());
    }
    Ok(())
}

/// Create one permissionless coherent checkpoint from
/// `[master, lane_0, ..., lane_7, checkpoint, payer, system_program]`.
/// Lane accounts are read-only. Only the fresh immutable checkpoint and the
/// master's checkpoint metadata are written.
pub(crate) fn process_pair_forest_checkpoint_with_runtime_v1<'info, R: PoolCpiRuntimeV1>(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'info>],
    instruction_data: &[u8],
    rent: &Rent,
    runtime: &mut R,
) -> ProgramResult {
    decode_pair_forest_checkpoint_instruction_v1(instruction_data)?;
    require_exact_account_count(accounts, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_COUNT)?;
    require_unique_accounts(accounts)?;
    let master = &accounts[FOREST_MASTER_ACCOUNT_INDEX];
    let lanes = &accounts[FOREST_FIRST_LANE_ACCOUNT_INDEX
        ..FOREST_FIRST_LANE_ACCOUNT_INDEX + POOL_V1_PAIR_FOREST_LANE_COUNT];
    let checkpoint = &accounts[FOREST_MINT_OR_CHECKPOINT_ACCOUNT_INDEX];
    let payer = &accounts[FOREST_CHECKPOINT_PAYER_ACCOUNT_INDEX];
    let system_program_account = &accounts[FOREST_CHECKPOINT_SYSTEM_ACCOUNT_INDEX];
    require_payer_and_system_program(payer, system_program_account)?;

    let planned = plan_pair_forest_checkpoint_accounts_v1(program_id, master, lanes, checkpoint)?;
    let preparation = plan_fresh_program_pda(
        checkpoint,
        program_id,
        &planned.checkpoint,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
    )?;
    if preparation == FreshPdaPreparationV1::CreateOrAllocateSystemOwned {
        let checkpoint_state = decode_pool_v1_pair_forest_checkpoint_v1(&planned.checkpoint_image)
            .map_err(|_| PoolV1ProgramError::StateHistoryMismatch)?;
        let sequence_bytes = checkpoint_state.checkpoint_sequence.to_le_bytes();
        let bump_bytes = [checkpoint_state.bump];
        let seeds: &[&[u8]] = &[
            POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,
            master.key.as_ref(),
            &sequence_bytes,
            &bump_bytes,
        ];
        create_or_allocate_pda(
            runtime,
            payer,
            checkpoint,
            system_program_account,
            POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
            program_id,
            seeds,
        )?;
    }
    require_program_owned_zeroed(
        checkpoint,
        program_id,
        POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES,
        rent,
    )?;

    let mut master_data = master.try_borrow_mut_data()?;
    let mut checkpoint_data = checkpoint.try_borrow_mut_data()?;
    checkpoint_data.copy_from_slice(&planned.checkpoint_image);
    master_data.copy_from_slice(&planned.next_master_image);
    Ok(())
}

/// Authenticate one retained immutable checkpoint account. Historical records
/// remain valid after later checkpoints; no comparison to a mutable "latest"
/// value is made here.
pub fn decode_retained_pair_forest_checkpoint_account_v1(
    program_id: &Pubkey,
    expected_master: &Pubkey,
    account: &AccountInfo<'_>,
) -> Result<PoolV1PairForestCheckpointV1, ProgramError> {
    require_program_account(account, program_id, false)?;
    if account.is_signer {
        return Err(ProgramError::InvalidAccountData);
    }
    let checkpoint = decode_pool_v1_pair_forest_checkpoint_v1(&account.try_borrow_data()?)
        .map_err(|_| PoolV1ProgramError::InvalidAccountType)?;
    // B4: the checkpoint stores its canonical bump at byte 7 (as the R1
    // verifier adapter reads it); one `create_program_address` authenticates
    // this existing Pool-owned image (F6). A mismatch keeps the old error.
    if checkpoint.master != expected_master.to_bytes()
        || !crate::registry::stored_bump_address_matches(
            &[
                POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,
                expected_master.as_ref(),
                &checkpoint.checkpoint_sequence.to_le_bytes(),
                &[checkpoint.bump],
            ],
            program_id,
            account.key,
        )
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    Ok(checkpoint)
}

#[cfg(test)]
mod tests {
    use std::{vec, vec::Vec};

    use aspis_core::field::M31;
    use aspis_statement::pool_v1::{
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1,
        encode_pool_v1_pair_forest_master_v1, encode_pool_v1_pair_forest_terminal_request_v1,
        IncrementalMerkleTreeV1, PoolIdentityV1, PoolV1PairForestTerminalPaymentV1,
        PoolV1PairForestTerminalRequestV1, PoolV1PairForestTerminalResultV1,
        PoolV1PairVerifiedAfterstateV1, PoolV1PrivateTransferPublicV1, PoolV1TransitionKind,
        PoolV1WithdrawalPublicV1, VerifierPolicyV1, POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES,
        POOL_V1_PAIR_FOREST_ALL_LANES_MASK, POOL_V1_PAIR_TREE_DEPTH,
    };
    use solana_program::{clock::Epoch, instruction::Instruction};
    use solana_sdk_ids::{bpf_loader, native_loader, system_program};

    use super::*;

    #[derive(Clone)]
    struct TestAccount {
        key: Pubkey,
        owner: Pubkey,
        lamports: u64,
        data: Vec<u8>,
        signer: bool,
        writable: bool,
        executable: bool,
    }

    impl TestAccount {
        fn info(&mut self) -> AccountInfo<'_> {
            AccountInfo::new(
                &self.key,
                self.signer,
                self.writable,
                &mut self.lamports,
                &mut self.data,
                &self.owner,
                self.executable,
                Epoch::default(),
            )
        }
    }

    struct NoCpi;

    impl PoolCpiRuntimeV1 for NoCpi {
        fn invoke<'info>(&mut self, _: &Instruction, _: &[AccountInfo<'info>]) -> ProgramResult {
            panic!("unexpected unsigned CPI")
        }

        fn invoke_signed<'info>(
            &mut self,
            _: &Instruction,
            _: &[AccountInfo<'info>],
            _: &[&[&[u8]]],
        ) -> ProgramResult {
            panic!("unexpected signed CPI")
        }
    }

    struct DepositCpi {
        apply_exact_delta: bool,
        calls: usize,
    }

    struct WithdrawalCpi {
        fail: bool,
        calls: usize,
    }

    struct MarkerSystemCpi {
        pool_program: Pubkey,
        calls: usize,
    }

    /// Host model of the System program's `*_with_seed` checks: the base must
    /// be a signer meta, `address == create_with_seed(base, seed, owner)`, the
    /// seed at most 32 bytes of UTF-8. Returns (base, seed, rest).
    fn parse_with_seed_prefix(data: &[u8]) -> Result<(Pubkey, std::string::String, &[u8]), ProgramError> {
        let base = Pubkey::new_from_array(
            data.get(4..36)
                .ok_or(ProgramError::InvalidInstructionData)?
                .try_into()
                .unwrap(),
        );
        let length = u64::from_le_bytes(
            data.get(36..44)
                .ok_or(ProgramError::InvalidInstructionData)?
                .try_into()
                .unwrap(),
        ) as usize;
        let seed_bytes = data
            .get(44..44 + length)
            .ok_or(ProgramError::InvalidInstructionData)?;
        let seed = std::string::String::from_utf8(seed_bytes.to_vec())
            .map_err(|_| ProgramError::InvalidInstructionData)?;
        if seed.len() > 32 {
            return Err(ProgramError::InvalidSeeds);
        }
        Ok((base, seed, &data[44 + length..]))
    }

    fn require_seed_address(
        instruction: &Instruction,
        address_meta: usize,
        base: &Pubkey,
        seed: &str,
        owner: &Pubkey,
    ) -> ProgramResult {
        let base_signs = instruction
            .accounts
            .iter()
            .any(|meta| meta.pubkey == *base && meta.is_signer);
        if !base_signs
            || Pubkey::create_with_seed(base, seed, owner).map_err(|_| ProgramError::InvalidSeeds)?
                != instruction.accounts[address_meta].pubkey
        {
            return Err(ProgramError::MissingRequiredSignature);
        }
        Ok(())
    }

    fn find_info<'a, 'info>(
        infos: &'a [AccountInfo<'info>],
        key: &Pubkey,
    ) -> Result<&'a AccountInfo<'info>, ProgramError> {
        infos
            .iter()
            .find(|info| info.key == key)
            .ok_or(ProgramError::NotEnoughAccountKeys)
    }

    impl MarkerSystemCpi {
        fn apply_system_instruction<'info>(
            &mut self,
            instruction: &Instruction,
            infos: &[AccountInfo<'info>],
        ) -> ProgramResult {
            if instruction.program_id != system_program::id() || instruction.data.len() < 4 {
                return Err(ProgramError::IncorrectProgramId);
            }
            self.calls += 1;
            let discriminant = u32::from_le_bytes(instruction.data[..4].try_into().unwrap());
            match discriminant {
                // SystemInstruction::CreateAccountWithSeed.
                3 => {
                    let (base, seed, rest) = parse_with_seed_prefix(&instruction.data)?;
                    if rest.len() != 48 || instruction.accounts.len() != 3 {
                        return Err(ProgramError::InvalidInstructionData);
                    }
                    let lamports = u64::from_le_bytes(rest[..8].try_into().unwrap());
                    let space = u64::from_le_bytes(rest[8..16].try_into().unwrap());
                    let owner = Pubkey::new_from_array(rest[16..48].try_into().unwrap());
                    require_seed_address(instruction, 1, &base, &seed, &owner)?;
                    if owner != self.pool_program {
                        return Err(ProgramError::InvalidInstructionData);
                    }
                    let payer = find_info(infos, &instruction.accounts[0].pubkey)?;
                    let created = find_info(infos, &instruction.accounts[1].pubkey)?;
                    find_info(infos, &base)?;
                    if created.lamports() != 0 {
                        // System `create_account`: "account already in use".
                        return Err(ProgramError::AccountAlreadyInitialized);
                    }
                    let mut payer_lamports = payer.try_borrow_mut_lamports()?;
                    if **payer_lamports < lamports {
                        return Err(ProgramError::InsufficientFunds);
                    }
                    **payer_lamports -= lamports;
                    **created.try_borrow_mut_lamports()? = lamports;
                    created.assign(&owner);
                    let data: &'static mut [u8] =
                        Box::leak(vec![0u8; usize::try_from(space).unwrap()].into_boxed_slice());
                    *created.data.borrow_mut() = data;
                    Ok(())
                }
                // SystemInstruction::AllocateWithSeed.
                9 => {
                    let (base, seed, rest) = parse_with_seed_prefix(&instruction.data)?;
                    if rest.len() != 40 || instruction.accounts.len() != 2 {
                        return Err(ProgramError::InvalidInstructionData);
                    }
                    let space = u64::from_le_bytes(rest[..8].try_into().unwrap());
                    let owner = Pubkey::new_from_array(rest[8..40].try_into().unwrap());
                    require_seed_address(instruction, 0, &base, &seed, &owner)?;
                    let account = find_info(infos, &instruction.accounts[0].pubkey)?;
                    find_info(infos, &base)?;
                    let data: &'static mut [u8] =
                        Box::leak(vec![0u8; usize::try_from(space).unwrap()].into_boxed_slice());
                    *account.data.borrow_mut() = data;
                    Ok(())
                }
                // SystemInstruction::AssignWithSeed.
                10 => {
                    let (base, seed, rest) = parse_with_seed_prefix(&instruction.data)?;
                    if rest.len() != 32 || instruction.accounts.len() != 2 {
                        return Err(ProgramError::InvalidInstructionData);
                    }
                    let owner = Pubkey::new_from_array(rest[..32].try_into().unwrap());
                    require_seed_address(instruction, 0, &base, &seed, &owner)?;
                    if owner != self.pool_program {
                        return Err(ProgramError::InvalidInstructionData);
                    }
                    let account = find_info(infos, &instruction.accounts[0].pubkey)?;
                    find_info(infos, &base)?;
                    account.assign(&owner);
                    Ok(())
                }
                // SystemInstruction::CreateAccount.
                0 => {
                    if instruction.data.len() != 52 || infos.len() != 3 {
                        return Err(ProgramError::InvalidInstructionData);
                    }
                    let lamports = u64::from_le_bytes(instruction.data[4..12].try_into().unwrap());
                    let space = u64::from_le_bytes(instruction.data[12..20].try_into().unwrap());
                    let owner =
                        Pubkey::new_from_array(instruction.data[20..52].try_into().unwrap());
                    if owner != self.pool_program
                        || instruction.accounts.len() != 2
                        || instruction.accounts[0].pubkey != *infos[0].key
                        || instruction.accounts[1].pubkey != *infos[1].key
                    {
                        return Err(ProgramError::InvalidInstructionData);
                    }
                    let mut payer_lamports = infos[0].try_borrow_mut_lamports()?;
                    if **payer_lamports < lamports {
                        return Err(ProgramError::InsufficientFunds);
                    }
                    **payer_lamports -= lamports;
                    **infos[1].try_borrow_mut_lamports()? = lamports;
                    infos[1].assign(&owner);
                    let data: &'static mut [u8] =
                        Box::leak(vec![0u8; usize::try_from(space).unwrap()].into_boxed_slice());
                    *infos[1].data.borrow_mut() = data;
                    Ok(())
                }
                // SystemInstruction::Transfer.
                2 => {
                    if instruction.data.len() != 12 || infos.len() < 3 {
                        return Err(ProgramError::InvalidInstructionData);
                    }
                    let lamports = u64::from_le_bytes(instruction.data[4..12].try_into().unwrap());
                    let mut payer_lamports = infos[0].try_borrow_mut_lamports()?;
                    if **payer_lamports < lamports {
                        return Err(ProgramError::InsufficientFunds);
                    }
                    **payer_lamports -= lamports;
                    let mut marker_lamports = infos[1].try_borrow_mut_lamports()?;
                    **marker_lamports = (**marker_lamports)
                        .checked_add(lamports)
                        .ok_or(PoolV1ProgramError::ArithmeticOverflow)?;
                    Ok(())
                }
                // SystemInstruction::Allocate.
                8 => {
                    if instruction.data.len() != 12 || infos.len() != 3 {
                        return Err(ProgramError::InvalidInstructionData);
                    }
                    let space = u64::from_le_bytes(instruction.data[4..12].try_into().unwrap());
                    let data: &'static mut [u8] =
                        Box::leak(vec![0u8; usize::try_from(space).unwrap()].into_boxed_slice());
                    *infos[1].data.borrow_mut() = data;
                    Ok(())
                }
                // SystemInstruction::Assign.
                1 => {
                    if instruction.data.len() != 36 || infos.len() != 3 {
                        return Err(ProgramError::InvalidInstructionData);
                    }
                    let owner = Pubkey::new_from_array(instruction.data[4..36].try_into().unwrap());
                    if owner != self.pool_program {
                        return Err(ProgramError::InvalidInstructionData);
                    }
                    infos[1].assign(&owner);
                    Ok(())
                }
                _ => Err(ProgramError::InvalidInstructionData),
            }
        }
    }

    impl PoolCpiRuntimeV1 for MarkerSystemCpi {
        fn invoke<'info>(
            &mut self,
            instruction: &Instruction,
            infos: &[AccountInfo<'info>],
        ) -> ProgramResult {
            self.apply_system_instruction(instruction, infos)
        }

        fn invoke_signed<'info>(
            &mut self,
            instruction: &Instruction,
            infos: &[AccountInfo<'info>],
            signer_seeds: &[&[&[u8]]],
        ) -> ProgramResult {
            if signer_seeds.len() != 1 || instruction.data.len() < 4 {
                return Err(ProgramError::InvalidSeeds);
            }
            let signer = Pubkey::create_program_address(signer_seeds[0], &self.pool_program)
                .map_err(|_| ProgramError::InvalidSeeds)?;
            let discriminant = u32::from_le_bytes(instruction.data[..4].try_into().unwrap());
            let signed_key = if matches!(discriminant, 3 | 9 | 10) {
                // `*_with_seed`: the PDA signs as the base.
                parse_with_seed_prefix(&instruction.data)?.0
            } else {
                *infos[1].key
            };
            if signer != signed_key {
                return Err(ProgramError::InvalidSeeds);
            }
            self.apply_system_instruction(instruction, infos)
        }
    }

    impl PoolCpiRuntimeV1 for WithdrawalCpi {
        fn invoke<'info>(&mut self, _: &Instruction, _: &[AccountInfo<'info>]) -> ProgramResult {
            panic!("unexpected unsigned CPI")
        }

        fn invoke_signed<'info>(
            &mut self,
            instruction: &Instruction,
            infos: &[AccountInfo<'info>],
            _: &[&[&[u8]]],
        ) -> ProgramResult {
            self.calls += 1;
            if self.fail {
                return Err(ProgramError::Custom(0xc057));
            }
            let amount = u64::from_le_bytes(
                instruction.data[1..9]
                    .try_into()
                    .map_err(|_| ProgramError::InvalidInstructionData)?,
            );
            let vault = u64::from_le_bytes(
                infos[0].try_borrow_data()?[64..72]
                    .try_into()
                    .map_err(|_| ProgramError::InvalidAccountData)?,
            );
            let destination = u64::from_le_bytes(
                infos[2].try_borrow_data()?[64..72]
                    .try_into()
                    .map_err(|_| ProgramError::InvalidAccountData)?,
            );
            crate::vault::write_token_amount_for_test(
                &infos[0],
                vault
                    .checked_sub(amount)
                    .ok_or(PoolV1ProgramError::ArithmeticOverflow)?,
            )?;
            crate::vault::write_token_amount_for_test(
                &infos[2],
                destination
                    .checked_add(amount)
                    .ok_or(PoolV1ProgramError::ArithmeticOverflow)?,
            )
        }
    }

    impl PoolCpiRuntimeV1 for DepositCpi {
        fn invoke<'info>(
            &mut self,
            instruction: &Instruction,
            infos: &[AccountInfo<'info>],
        ) -> ProgramResult {
            assert_eq!(instruction.program_id, LEGACY_SPL_TOKEN_PROGRAM_ID);
            assert_eq!(instruction.data.len(), 10);
            assert_eq!(instruction.data[0], 12);
            assert_eq!(infos.len(), 5);
            self.calls += 1;
            if !self.apply_exact_delta {
                return Ok(());
            }
            let amount = u64::from_le_bytes(instruction.data[1..9].try_into().unwrap());
            let source_before =
                u64::from_le_bytes(infos[0].try_borrow_data()?[64..72].try_into().unwrap());
            let vault_before =
                u64::from_le_bytes(infos[2].try_borrow_data()?[64..72].try_into().unwrap());
            crate::vault::write_token_amount_for_test(
                &infos[0],
                source_before.checked_sub(amount).unwrap(),
            )?;
            crate::vault::write_token_amount_for_test(
                &infos[2],
                vault_before.checked_add(amount).unwrap(),
            )
        }

        fn invoke_signed<'info>(
            &mut self,
            _: &Instruction,
            _: &[AccountInfo<'info>],
            _: &[&[&[u8]]],
        ) -> ProgramResult {
            panic!("unexpected signed CPI")
        }
    }

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31(seed + 13 * index as u32))
    }

    fn master(program_id: Pubkey, mint: Pubkey) -> (Pubkey, PoolV1PairForestMasterV1) {
        let (key, bump) = pool_v1_pair_forest_master_address(&program_id, &mint);
        (
            key,
            PoolV1PairForestMasterV1 {
                bump,
                identity: PoolIdentityV1 {
                    pool: key.to_bytes(),
                    asset_mint: mint.to_bytes(),
                    token_program: [3u8; 32],
                    asset_id: M31(4),
                    deployment_domain: [5u8; 32],
                },
                verifier_policy: VerifierPolicyV1 {
                    flags: 1,
                    registry_program: [6u8; 32],
                    registry_authority: [0u8; 32],
                    policy_binding: [7u8; 32],
                },
                initialized_lane_mask: POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
                has_checkpoint: false,
                next_checkpoint_sequence: 0,
                last_checkpoint_lane_sequences: [0u64; 8],
            },
        )
    }

    fn canonical_genesis_lane(
        program_id: &Pubkey,
        master: &Pubkey,
        lane_id: u8,
    ) -> PoolV1PairForestLaneStateV1 {
        let bump = pool_v1_pair_forest_lane_address(program_id, master, lane_id)
            .unwrap()
            .1;
        genesis_lane_state(master, lane_id, bump)
    }

    fn lane_state(program_id: Pubkey, master: Pubkey, lane: u8) -> PoolV1PairForestLaneStateV1 {
        PoolV1PairForestLaneStateV1 {
            bump: pool_v1_pair_forest_lane_address(&program_id, &master, lane)
                .unwrap()
                .1,
            master: master.to_bytes(),
            lane_id: lane,
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: 0,
                root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH],
                frontier: core::array::from_fn(|level| POOL_V1_PAIR_EMPTY_ROOTS[level]),
            },
        }
    }

    #[cfg(any(
        feature = "pair-forest-source-invariant-audit",
        feature = "pair-forest-deposit-invariant-audit"
    ))]
    #[test]
    fn program_invariant_lane_decoder_keeps_exact_boundary() {
        let program_id = Pubkey::new_unique();
        let master = Pubkey::new_unique();
        let lane_id = 3;
        let mut lane = lane_state(program_id, master, lane_id);
        for leaf in 0..13 {
            lane.tree = lane
                .tree
                .append_one_with_empty_roots(digest(20_000 + leaf), &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap()
                .0;
        }
        let canonical =
            encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS).unwrap();
        let lane_key = pool_v1_pair_forest_lane_address(&program_id, &master, lane_id)
            .unwrap()
            .0;
        let mut account = TestAccount {
            key: lane_key,
            owner: program_id,
            lamports: 1,
            data: canonical.to_vec(),
            signer: false,
            writable: true,
            executable: false,
        };
        assert_eq!(
            decode_lane_account_from_program_invariant_v1(
                &program_id,
                &master,
                lane_id,
                &account.info(),
                true,
            )
            .unwrap(),
            lane,
        );

        // Canonical digest encoding and capacity remain fail-closed even
        // though this decoder consumes the persisted root/frontier invariant.
        let root_start = POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES + 16;
        let canonical_root = account.data[root_start..root_start + 32].to_vec();
        account.data[root_start..root_start + 4]
            .copy_from_slice(&aspis_core::field::P.to_le_bytes());
        assert!(decode_lane_account_from_program_invariant_v1(
            &program_id,
            &master,
            lane_id,
            &account.info(),
            true,
        )
        .is_err());
        account.data[root_start..root_start + 32].copy_from_slice(&canonical_root);

        let index_start = POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES + 8;
        let canonical_index = account.data[index_start..index_start + 8].to_vec();
        account.data[index_start..index_start + 8]
            .copy_from_slice(&(POOL_V1_PAIR_CAPACITY + 1).to_le_bytes());
        assert!(decode_lane_account_from_program_invariant_v1(
            &program_id,
            &master,
            lane_id,
            &account.info(),
            true,
        )
        .is_err());
        account.data[index_start..index_start + 8].copy_from_slice(&canonical_index);

        // The one explicit boundary is real: a canonical but inconsistent
        // active root is accepted here and rejected by the generic codec.
        // Every invariant-backed caller additionally binds this root to the
        // Pool-owned current history entry before CPI.
        account.data[root_start..root_start + 32]
            .copy_from_slice(&encode_digest_canonical(&digest(90_000)));
        assert!(
            decode_pool_v1_pair_forest_lane_state_v1(&account.data, &POOL_V1_PAIR_EMPTY_ROOTS,)
                .is_err()
        );
        assert!(decode_lane_account_from_program_invariant_v1(
            &program_id,
            &master,
            lane_id,
            &account.info(),
            true,
        )
        .is_ok());

        // Canonical inactive frontier slots are still enforced exactly.
        let inactive_level = 1usize;
        let inactive_start = POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES + 48 + 32 * inactive_level;
        account.data[inactive_start..inactive_start + 32]
            .copy_from_slice(&encode_digest_canonical(&digest(91_000)));
        assert!(decode_lane_account_from_program_invariant_v1(
            &program_id,
            &master,
            lane_id,
            &account.info(),
            true,
        )
        .is_err());
    }

    #[cfg(any(
        feature = "pair-forest-source-result-invariant-audit",
        feature = "pair-forest-deposit-invariant-audit"
    ))]
    #[test]
    fn authenticated_result_encoder_is_byte_exact_for_valid_lanes() {
        let program_id = Pubkey::new_unique();
        let master = Pubkey::new_unique();
        let mut lane = lane_state(program_id, master, 4);
        for leaf in 0..14 {
            lane.tree = lane
                .tree
                .append_one_with_empty_roots(digest(30_000 + leaf), &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap()
                .0;
        }
        assert_eq!(
            encode_lane_from_authenticated_result_v1(&lane).unwrap(),
            encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS).unwrap(),
        );
        lane.tree.frontier[0] = digest(99_000);
        assert!(encode_lane_from_authenticated_result_v1(&lane).is_err());
    }

    #[cfg(feature = "pair-forest-deposit-invariant-audit")]
    #[test]
    fn deposit_invariant_append_is_byte_exact_at_measured_boundaries() {
        let program_id = Pubkey::new_unique();
        let master = Pubkey::new_unique();
        let lane_id = 2;
        let mut lane = lane_state(program_id, master, lane_id);
        let measured = [0u64, 1, 2, 3, 7, 15, 255];

        for source_index in 0u64..=255 {
            let pair_leaf = digest(40_000 + source_index as u32);
            if measured.contains(&source_index) {
                let (strict_tree, strict_receipt) = lane
                    .tree
                    .append_one_with_empty_roots(pair_leaf, &POOL_V1_PAIR_EMPTY_ROOTS)
                    .unwrap();
                let strict_lane = PoolV1PairForestLaneStateV1 {
                    bump: lane.bump,
                    master: master.to_bytes(),
                    lane_id,
                    tree: strict_tree,
                };
                let strict_image = encode_pool_v1_pair_forest_lane_state_v1(
                    &strict_lane,
                    &POOL_V1_PAIR_EMPTY_ROOTS,
                )
                .unwrap();
                let (audit_receipt, audit_image) =
                    prepare_deposit_append_v1(&lane, lane_id, pair_leaf).unwrap();
                assert_eq!(audit_receipt, strict_receipt, "receipt at {source_index}");
                assert_eq!(
                    audit_image.as_ref(),
                    &strict_image,
                    "image at {source_index}"
                );
                assert_eq!(
                    decode_pool_v1_pair_forest_lane_state_v1(
                        audit_image.as_ref(),
                        &POOL_V1_PAIR_EMPTY_ROOTS,
                    )
                    .unwrap(),
                    strict_lane,
                    "strict successor decode at {source_index}",
                );
            }

            lane.tree = append_pair_leaf_from_program_invariant_v1(&lane.tree, pair_leaf)
                .unwrap()
                .0;
        }
    }

    #[cfg(feature = "pair-forest-deposit-invariant-audit")]
    #[test]
    fn deposit_invariant_append_rejects_full_tree_and_noncanonical_leaf() {
        let program_id = Pubkey::new_unique();
        let master = Pubkey::new_unique();
        let mut full = lane_state(program_id, master, 0).tree;
        full.next_leaf_index = POOL_V1_PAIR_CAPACITY;
        assert_eq!(
            append_pair_leaf_from_program_invariant_v1(&full, digest(50_000)),
            Err(PoolV1ProgramError::TreeFull.into()),
        );

        let genesis = lane_state(program_id, master, 0).tree;
        let mut noncanonical = digest(50_001);
        noncanonical[0] = M31(aspis_core::field::P);
        assert_eq!(
            append_pair_leaf_from_program_invariant_v1(&genesis, noncanonical),
            Err(PoolV1ProgramError::NonCanonicalLeaf.into()),
        );

        let mut oversized_lane = lane_state(program_id, master, 0);
        oversized_lane.tree.next_leaf_index = POOL_V1_PAIR_CAPACITY + 1;
        assert!(encode_lane_from_authenticated_result_v1(&oversized_lane).is_err());
    }

    #[test]
    fn pair_forest_lane_persistence_surface_remains_closed() {
        let source = include_str!("pair_forest.rs");
        let transition_write =
            ["lane_data", ".copy_from_slice(next_lane_image.as_ref());"].concat();
        let genesis_write = [
            "lane_data[lane]",
            ".copy_from_slice(lane_images[lane].as_ref());",
        ]
        .concat();
        assert_eq!(source.matches(&transition_write).count(), 2);
        assert_eq!(source.matches(&genesis_write).count(), 1);
    }

    fn fixtures(program_id: Pubkey) -> (TestAccount, [TestAccount; 8], TestAccount, Pubkey) {
        let mint = Pubkey::new_unique();
        let (master_key, master) = master(program_id, mint);
        let master_account = TestAccount {
            key: master_key,
            owner: program_id,
            lamports: 1,
            data: encode_pool_v1_pair_forest_master_v1(&master)
                .unwrap()
                .to_vec(),
            signer: false,
            writable: true,
            executable: false,
        };
        let lanes = core::array::from_fn(|lane| TestAccount {
            key: pool_v1_pair_forest_lane_address(&program_id, &master_key, lane as u8)
                .unwrap()
                .0,
            owner: program_id,
            lamports: 1,
            data: encode_pool_v1_pair_forest_lane_state_v1(
                &lane_state(program_id, master_key, lane as u8),
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .unwrap()
            .to_vec(),
            signer: false,
            writable: false,
            executable: false,
        });
        let checkpoint_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0).0;
        let checkpoint = TestAccount {
            key: checkpoint_key,
            owner: program_id,
            lamports: 1,
            data: vec![0u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES],
            signer: false,
            writable: true,
            executable: false,
        };
        (master_account, lanes, checkpoint, master_key)
    }

    fn forest_initialization(mint: Pubkey) -> PoolInitializationV1 {
        PoolInitializationV1 {
            asset_mint: mint.to_bytes(),
            token_program: LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),
            asset_id: M31(4),
            deployment_domain: [5u8; 32],
            verifier_policy: VerifierPolicyV1 {
                flags: 1,
                registry_program: [6u8; 32],
                registry_authority: [0u8; 32],
                policy_binding: [7u8; 32],
            },
        }
    }

    fn initialized_mint_data() -> Vec<u8> {
        let mut data = vec![0u8; LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES];
        data[45] = 1;
        data
    }

    fn initialized_token_data(mint: Pubkey, authority: Pubkey, amount: u64) -> Vec<u8> {
        let mut data = vec![0u8; crate::vault::LEGACY_SPL_TOKEN_ACCOUNT_BYTES];
        data[..32].copy_from_slice(mint.as_ref());
        data[32..64].copy_from_slice(authority.as_ref());
        data[64..72].copy_from_slice(&amount.to_le_bytes());
        data[108] = 1;
        data
    }

    /// Exact terminal instruction data `ASQ8 || canonical bump hints`.
    fn terminal_instruction(
        program_id: &Pubkey,
        request: &PoolV1PairForestTerminalRequestV1,
        lane_key: &Pubkey,
        next_leaf_index: u64,
    ) -> Vec<u8> {
        let withdrawal = matches!(
            request.public,
            PoolV1PairForestTerminalPaymentV1::Withdrawal(_)
        );
        let master = Pubkey::new_from_array(match request.public {
            PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => public.pool,
            PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => public.pool,
        });
        encode_pair_forest_terminal_instruction_data_v1(
            &encode_pool_v1_pair_forest_terminal_request_v1(request).unwrap(),
            pool_v1_pair_forest_terminal_bump_hints_v1(
                program_id,
                &master,
                lane_key,
                next_leaf_index,
                withdrawal,
            ),
        )
    }

    fn rent_lamports(bytes: usize) -> u64 {
        Rent::default().minimum_balance(bytes).max(1)
    }

    fn append_test_verifier_checkpoint(accounts: &mut Vec<TestAccount>) {
        if cfg!(feature = "r1-split-checkpoint") {
            // These fixtures have one history page and retain the V7 indices.
            accounts.push(TestAccount {
                key: Pubkey::new_unique(),
                owner: accounts[9].key,
                lamports: 1,
                data: vec![7; 1_768],
                signer: false,
                writable: false,
                executable: false,
            });
        }
    }

    fn terminal_base_accounts(
        program_id: Pubkey,
        master_key: Pubkey,
        master_state: &PoolV1PairForestMasterV1,
        checkpoint_key: Pubkey,
        checkpoint: &PoolV1PairForestCheckpointV1,
        lane_key: Pubkey,
        lane: &PoolV1PairForestLaneStateV1,
        marker_key: Pubkey,
    ) -> Vec<TestAccount> {
        let page_key = pool_v1_root_page_address(&program_id, &lane_key, 0).0;
        vec![
            TestAccount {
                key: master_key,
                owner: program_id,
                lamports: 1,
                data: encode_pool_v1_pair_forest_master_v1(master_state)
                    .unwrap()
                    .to_vec(),
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: checkpoint_key,
                owner: program_id,
                lamports: 1,
                data: encode_pool_v1_pair_forest_checkpoint_v1(checkpoint)
                    .unwrap()
                    .to_vec(),
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: lane_key,
                owner: program_id,
                lamports: 1,
                data: encode_pool_v1_pair_forest_lane_state_v1(lane, &POOL_V1_PAIR_EMPTY_ROOTS)
                    .unwrap()
                    .to_vec(),
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: page_key,
                owner: program_id,
                lamports: 1,
                data: vec![0; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: marker_key,
                owner: program_id,
                lamports: rent_lamports(POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES),
                data: vec![0; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: system_program::id(),
                lamports: 10 * rent_lamports(POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES),
                data: vec![],
                signer: true,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: system_program::id(),
                owner: native_loader::id(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: true,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: Pubkey::new_unique(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: Pubkey::new_unique(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: bpf_loader::id(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: true,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: Pubkey::new_unique(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
        ]
    }

    fn system_marker_terminal_transfer_fixture(
        program_id: Pubkey,
    ) -> (Vec<TestAccount>, Vec<u8>, PoolV1PairForestTerminalResultV1) {
        let mint = Pubkey::new_unique();
        let (master_key, mut master_state) = master(program_id, mint);
        master_state.identity.token_program = LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes();
        master_state.has_checkpoint = true;
        master_state.next_checkpoint_sequence = 1;
        let nullifier = digest(77);
        let lane_id =
            aspis_statement::pool_v1::pool_v1_pair_forest_output_lane_v1(&nullifier).unwrap();
        let lane_key = pool_v1_pair_forest_lane_address(&program_id, &master_key, lane_id)
            .unwrap()
            .0;
        let lane = canonical_genesis_lane(&program_id, &master_key, lane_id);
        let next_tree = lane
            .tree
            .append_one_with_empty_roots(digest(9_777), &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        let checkpoint = PoolV1PairForestCheckpointV1 {
            bump: pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0).1,
            master: master_key.to_bytes(),
            deployment_domain: master_state.identity.deployment_domain,
            checkpoint_sequence: 0,
            global_root: digest(7_777),
            lane_sequences: [0; 8],
        };
        let checkpoint_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0).0;
        let request = PoolV1PairForestTerminalRequestV1 {
            verifier_profile: [81; 32],
            verifier_release: [82; 32],
            pool_program: program_id.to_bytes(),
            public: PoolV1PairForestTerminalPaymentV1::PrivateTransfer(
                PoolV1PrivateTransferPublicV1 {
                    pool: master_key.to_bytes(),
                    deployment_domain: master_state.identity.deployment_domain,
                    anchor_sequence: 0,
                    anchor_root: checkpoint.global_root,
                    nullifier,
                    asset_id: master_state.identity.asset_id,
                    recipient_commitment: digest(8_001),
                    change_commitment: digest(8_002),
                },
            ),
        };
        let result = PoolV1PairForestTerminalResultV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            master_account: master_key.to_bytes(),
            selected_lane_account: lane_key.to_bytes(),
            output_lane: lane_id,
            nullifier,
            verified_afterstate: PoolV1PairVerifiedAfterstateV1 {
                next_pair_index: next_tree.next_leaf_index,
                next_root: next_tree.root,
                next_frontier: next_tree.frontier,
            },
        };
        let marker_key = crate::pool_v1_pair_forest_nullifier_marker_address(
            &program_id,
            &master_key,
            &aspis_statement::encode_digest_canonical(&nullifier),
        )
        .unwrap()
        .0;
        let mut accounts = terminal_base_accounts(
            program_id,
            master_key,
            &master_state,
            checkpoint_key,
            &checkpoint,
            lane_key,
            &lane,
            marker_key,
        );
        accounts[4].owner = system_program::id();
        accounts[4].lamports = 0;
        accounts[4].data.clear();
        append_test_verifier_checkpoint(&mut accounts);
        (
            accounts,
            terminal_instruction(&program_id, &request, &lane_key, 0),
            result,
        )
    }

    #[test]
    fn terminal_layout_keeps_proof_and_token_indices_with_optional_checkpoint() {
        let program_id = Pubkey::new_unique();
        for page_kind in 0..3 {
            for withdrawal in [false, true] {
                let (mut accounts, _, _) = system_marker_terminal_transfer_fixture(program_id);
                let mut lane = decode_pool_v1_pair_forest_lane_state_v1(
                    &accounts[2].data,
                    &POOL_V1_PAIR_EMPTY_ROOTS,
                )
                .unwrap();
                let lane_key = accounts[2].key;
                if page_kind != 0 {
                    // This tests account layout, not a tree transition: repeated
                    // retained roots supply only the page/sequence premises.
                    lane.tree.next_leaf_index = if page_kind == 1 { 1 } else { 255 };
                    let roots = vec![lane.tree.root; lane.tree.next_leaf_index as usize + 1];
                    write_new_page_unchecked(&mut accounts[3].data, &lane_key, 0, 0, &roots);
                }
                if page_kind == 2 {
                    accounts[3].writable = false;
                    accounts.insert(
                        4,
                        TestAccount {
                            key: pool_v1_root_page_address(&program_id, &lane_key, 1).0,
                            owner: program_id,
                            lamports: 1,
                            data: vec![0; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
                            signer: false,
                            writable: true,
                            executable: false,
                        },
                    );
                }
                let shift = usize::from(page_kind == 2);
                let token_start = 11 + shift;
                if withdrawal {
                    for offset in 0..5 {
                        accounts.insert(
                            token_start + offset,
                            TestAccount {
                                key: Pubkey::new_unique(),
                                owner: program_id,
                                lamports: 1,
                                data: vec![],
                                signer: false,
                                writable: false,
                                executable: false,
                            },
                        );
                    }
                }
                let legacy_count = token_start + if withdrawal { 5 } else { 0 };
                let checkpoint_index =
                    cfg!(feature = "r1-split-checkpoint").then_some(legacy_count);
                let hints = pool_v1_pair_forest_terminal_bump_hints_v1(
                    &program_id,
                    &accounts[0].key,
                    &lane_key,
                    lane.tree.next_leaf_index,
                    false,
                );
                let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
                let layout =
                    plan_pair_forest_spend_layout_v1(&program_id, &infos, &lane, withdrawal, hints)
                        .unwrap();
                assert_eq!(layout.verifier_index, 9 + shift);
                assert_eq!(layout.proof_index, 10 + shift);
                assert_eq!(layout.token_start, token_start);
                assert_eq!(layout.verifier_checkpoint_index, checkpoint_index);
                assert_eq!(
                    infos.len(),
                    legacy_count + usize::from(checkpoint_index.is_some())
                );
                assert!(plan_pair_forest_spend_layout_v1(
                    &program_id,
                    &infos[..infos.len() - 1],
                    &lane,
                    withdrawal,
                    hints,
                )
                .is_err());
                let mut extra = infos.clone();
                extra.push(infos[0].clone());
                assert!(
                    plan_pair_forest_spend_layout_v1(&program_id, &extra, &lane, withdrawal, hints)
                        .is_err()
                );
                if let Some(index) = checkpoint_index {
                    // The checkpoint cannot alias any preceding top-level account,
                    // including the existing Pool checkpoint and custody accounts.
                    for previous in 0..index {
                        let mut aliased = infos.clone();
                        aliased[index].key = infos[previous].key;
                        assert!(plan_pair_forest_spend_layout_v1(
                            &program_id,
                            &aliased,
                            &lane,
                            withdrawal,
                            hints,
                        )
                        .is_err());
                    }
                }
            }
        }
    }

    fn initialization_accounts(program_id: Pubkey, mint: Pubkey) -> Vec<TestAccount> {
        let master = pool_v1_pair_forest_master_address(&program_id, &mint).0;
        let mut accounts = Vec::with_capacity(POOL_V1_PAIR_FOREST_INITIALIZE_ACCOUNT_COUNT);
        accounts.push(TestAccount {
            key: master,
            owner: program_id,
            lamports: rent_lamports(POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES),
            data: vec![0u8; POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES],
            signer: false,
            writable: true,
            executable: false,
        });
        for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
            accounts.push(TestAccount {
                key: pool_v1_pair_forest_lane_address(&program_id, &master, lane as u8)
                    .unwrap()
                    .0,
                owner: program_id,
                lamports: rent_lamports(
                    aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
                ),
                data: vec![0u8; aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            });
        }
        accounts.push(TestAccount {
            key: mint,
            owner: LEGACY_SPL_TOKEN_PROGRAM_ID,
            lamports: 1,
            data: initialized_mint_data(),
            signer: false,
            writable: false,
            executable: false,
        });
        let vault_authority = crate::pool_v1_vault_authority_address(&program_id, &master).0;
        accounts.push(TestAccount {
            key: crate::pool_v1_vault_token_account_address(&program_id, &master).0,
            owner: LEGACY_SPL_TOKEN_PROGRAM_ID,
            lamports: rent_lamports(crate::vault::LEGACY_SPL_TOKEN_ACCOUNT_BYTES),
            data: initialized_token_data(mint, vault_authority, 0),
            signer: false,
            writable: true,
            executable: false,
        });
        accounts.push(TestAccount {
            key: LEGACY_SPL_TOKEN_PROGRAM_ID,
            owner: bpf_loader::id(),
            lamports: 1,
            data: Vec::new(),
            signer: false,
            writable: false,
            executable: true,
        });
        accounts.push(TestAccount {
            key: Pubkey::new_unique(),
            owner: system_program::id(),
            lamports: 1_000_000_000,
            data: Vec::new(),
            signer: true,
            writable: true,
            executable: false,
        });
        accounts.push(TestAccount {
            key: system_program::id(),
            owner: native_loader::id(),
            lamports: 1,
            data: Vec::new(),
            signer: false,
            writable: false,
            executable: true,
        });
        accounts
    }

    fn genesis_deposit_fixture(
        program_id: Pubkey,
        mint: Pubkey,
    ) -> (Vec<TestAccount>, Vec<u8>, u8, Digest) {
        let initialization = forest_initialization(mint);
        let mut initialized = initialization_accounts(program_id, mint);
        let initialize_instruction =
            encode_pair_forest_initialize_instruction_v1(&initialization).unwrap();
        {
            let infos: Vec<_> = initialized.iter_mut().map(TestAccount::info).collect();
            process_pair_forest_initialize_with_runtime_v1(
                &program_id,
                &infos,
                &initialize_instruction,
                &Rent::default(),
                &mut NoCpi,
            )
            .unwrap();
        }
        let request = DepositRequestV1 {
            owner_key: digest(700),
            amount: 7,
            salt: digest(900),
            encrypted_note_payload: b"forest-note",
        };
        let commitment = pool_v1_note_commitment(
            &request.owner_key,
            request.amount,
            initialization.asset_id,
            &request.salt,
        );
        let lane_id = pool_v1_pair_forest_deposit_lane_v1(&commitment).unwrap();
        let instruction = encode_pair_forest_deposit_instruction_v1(&request).unwrap();
        let master_key = initialized[0].key;
        let lane_key = initialized[1 + usize::from(lane_id)].key;
        let source_authority = Pubkey::new_unique();
        let source = Pubkey::new_unique();
        let mut master = initialized[0].clone();
        master.writable = false;
        let mut lane = initialized[1 + usize::from(lane_id)].clone();
        lane.writable = true;
        let accounts = vec![
            master,
            lane,
            TestAccount {
                key: pool_v1_root_page_address(&program_id, &lane_key, 0).0,
                owner: program_id,
                lamports: rent_lamports(POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES),
                data: vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            },
            initialized[9].clone(),
            TestAccount {
                key: source,
                owner: LEGACY_SPL_TOKEN_PROGRAM_ID,
                lamports: 1,
                data: initialized_token_data(mint, source_authority, 100),
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: source_authority,
                owner: system_program::id(),
                lamports: 1,
                data: Vec::new(),
                signer: true,
                writable: false,
                executable: false,
            },
            initialized[10].clone(),
            initialized[11].clone(),
            initialized[12].clone(),
            initialized[13].clone(),
        ];
        assert_eq!(accounts[0].key, master_key);
        (accounts, instruction, lane_id, commitment)
    }

    #[test]
    fn instruction_wires_are_exact_versioned_and_trailing_closed() {
        let initialization = forest_initialization(Pubkey::new_unique());
        let encoded = encode_pair_forest_initialize_instruction_v1(&initialization).unwrap();
        assert_eq!(encoded.len(), POOL_V1_INITIALIZE_INSTRUCTION_BYTES);
        assert_eq!(
            decode_pair_forest_initialize_instruction_v1(&encoded),
            Ok(initialization)
        );
        let mut wrong_lane_count = encoded;
        wrong_lane_count[5] = 7;
        assert!(decode_pair_forest_initialize_instruction_v1(&wrong_lane_count).is_err());
        let mut trailing = encoded.to_vec();
        trailing.push(0);
        assert!(decode_pair_forest_initialize_instruction_v1(&trailing).is_err());

        let checkpoint = encode_pair_forest_checkpoint_instruction_v1();
        assert_eq!(
            decode_pair_forest_checkpoint_instruction_v1(&checkpoint),
            Ok(())
        );
        let mut wrong_version = checkpoint;
        wrong_version[4] = 2;
        assert_eq!(
            decode_pair_forest_checkpoint_instruction_v1(&wrong_version),
            Err(ProgramError::InvalidInstructionData)
        );

        let request = DepositRequestV1 {
            owner_key: digest(100),
            amount: 7,
            salt: digest(200),
            encrypted_note_payload: b"forest-note",
        };
        let deposit = encode_pair_forest_deposit_instruction_v1(&request).unwrap();
        assert_eq!(&deposit[..4], b"AS8D");
        assert_eq!(
            decode_pair_forest_deposit_instruction_v1(&deposit),
            Ok(request)
        );
        let mut wrong_magic = deposit.clone();
        wrong_magic[..4].copy_from_slice(b"ASDI");
        assert!(decode_pair_forest_deposit_instruction_v1(&wrong_magic).is_err());
        let mut deposit_trailing = deposit;
        deposit_trailing.push(0);
        assert!(decode_pair_forest_deposit_instruction_v1(&deposit_trailing).is_err());
    }

    #[test]
    fn global_root_is_exact_seven_parent_fixed_order_tree() {
        let roots = core::array::from_fn(|lane| digest(100 + 100 * lane as u32));
        let first = [
            pool_v1_tree_parent(&roots[0], &roots[1]),
            pool_v1_tree_parent(&roots[2], &roots[3]),
            pool_v1_tree_parent(&roots[4], &roots[5]),
            pool_v1_tree_parent(&roots[6], &roots[7]),
        ];
        let second = [
            pool_v1_tree_parent(&first[0], &first[1]),
            pool_v1_tree_parent(&first[2], &first[3]),
        ];
        assert_eq!(
            pool_v1_pair_forest_global_root_v1(&roots),
            pool_v1_tree_parent(&second[0], &second[1])
        );
        let mut swapped = roots;
        swapped.swap(0, 1);
        assert_ne!(
            pool_v1_pair_forest_global_root_v1(&roots),
            pool_v1_pair_forest_global_root_v1(&swapped)
        );
    }

    #[test]
    fn precreated_initialize_writes_exact_master_and_all_eight_genesis_lanes() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let initialization = forest_initialization(mint);
        let instruction = encode_pair_forest_initialize_instruction_v1(&initialization).unwrap();
        let mut accounts = initialization_accounts(program_id, mint);
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        process_pair_forest_initialize_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut NoCpi,
        )
        .unwrap();
        drop(infos);

        let decoded_master = decode_pool_v1_pair_forest_master_v1(&accounts[0].data).unwrap();
        assert_eq!(decoded_master.identity.asset_mint, mint.to_bytes());
        assert_eq!(decoded_master.identity.deployment_domain, [5u8; 32]);
        assert_eq!(decoded_master.initialized_lane_mask, 0xff);
        assert_eq!(
            decoded_master.bump,
            pool_v1_pair_forest_master_address(&program_id, &mint).1
        );
        assert!(!decoded_master.has_checkpoint);
        for lane in 0..POOL_V1_PAIR_FOREST_LANE_COUNT {
            let decoded = decode_pool_v1_pair_forest_lane_state_v1(
                &accounts[1 + lane].data,
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .unwrap();
            assert_eq!(
                decoded,
                canonical_genesis_lane(&program_id, &accounts[0].key, lane as u8)
            );
        }
    }

    #[test]
    fn canonical_bumps_persist_for_system_and_precreated_accounts() {
        // The System allocation helper obtains rent through Rent::get(); the
        // native fixture supplies the same rent used for its precreated path.
        struct RentStub;
        impl solana_program::program_stubs::SyscallStubs for RentStub {
            fn sol_get_rent_sysvar(&self, address: *mut u8) -> u64 {
                // Solana's Sysvar::get passes a writable, aligned Rent pointer.
                unsafe { address.cast::<Rent>().write(Rent::default()) };
                0
            }
        }
        struct RestoreStubs(Option<Box<dyn solana_program::program_stubs::SyscallStubs>>);
        impl Drop for RestoreStubs {
            fn drop(&mut self) {
                if let Some(previous) = self.0.take() {
                    solana_program::program_stubs::set_syscall_stubs(previous);
                }
            }
        }
        let _restore = RestoreStubs(Some(solana_program::program_stubs::set_syscall_stubs(
            Box::new(RentStub),
        )));
        for create in [false, true] {
            let program_id = Pubkey::new_unique();
            let mint = Pubkey::new_unique();
            let mut accounts = initialization_accounts(program_id, mint);
            if create {
                for account in &mut accounts[..9] {
                    account.owner = system_program::id();
                    account.lamports = 0;
                    account.data.clear();
                }
            }
            let (master_key, master_bump) = pool_v1_pair_forest_master_address(&program_id, &mint);
            let (checkpoint_key, checkpoint_bump) =
                pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0);
            let mut checkpoint = TestAccount {
                key: checkpoint_key,
                owner: if create {
                    system_program::id()
                } else {
                    program_id
                },
                lamports: if create {
                    0
                } else {
                    rent_lamports(POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES)
                },
                data: if create {
                    vec![]
                } else {
                    vec![0; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES]
                },
                signer: false,
                writable: true,
                executable: false,
            };
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            let mut runtime = MarkerSystemCpi {
                pool_program: program_id,
                calls: 0,
            };
            process_pair_forest_initialize_with_runtime_v1(
                &program_id,
                &infos,
                &encode_pair_forest_initialize_instruction_v1(&forest_initialization(mint))
                    .unwrap(),
                &Rent::default(),
                &mut runtime,
            )
            .unwrap();
            let decoded = decode_master_account(&program_id, &infos[0], true).unwrap();
            assert_eq!(decoded.bump, master_bump);
            let mut checkpoint_infos = infos[..9].to_vec();
            for (lane, info) in checkpoint_infos[1..9].iter_mut().enumerate() {
                info.is_writable = false;
                let state =
                    decode_lane_account(&program_id, &master_key, lane as u8, info, false).unwrap();
                assert_eq!(
                    state.bump,
                    pool_v1_pair_forest_lane_address(&program_id, &master_key, lane as u8)
                        .unwrap()
                        .1
                );
            }
            let lane_images: Vec<_> = checkpoint_infos[1..9]
                .iter()
                .map(|info| info.try_borrow_data().unwrap().to_vec())
                .collect();
            checkpoint_infos.push(checkpoint.info());
            checkpoint_infos.push(infos[12].clone());
            checkpoint_infos.push(infos[13].clone());
            process_pair_forest_checkpoint_with_runtime_v1(
                &program_id,
                &checkpoint_infos,
                &encode_pair_forest_checkpoint_instruction_v1(),
                &Rent::default(),
                &mut runtime,
            )
            .unwrap();
            assert_eq!(runtime.calls, if create { 10 } else { 0 });
            assert_eq!(
                decode_master_account(&program_id, &infos[0], true)
                    .unwrap()
                    .bump,
                master_bump
            );
            checkpoint_infos[9].is_writable = false;
            assert_eq!(
                decode_retained_pair_forest_checkpoint_account_v1(
                    &program_id,
                    &master_key,
                    &checkpoint_infos[9]
                )
                .unwrap()
                .bump,
                checkpoint_bump
            );
            for (lane, image) in lane_images.iter().enumerate() {
                assert_eq!(
                    checkpoint_infos[1 + lane]
                        .try_borrow_data()
                        .unwrap()
                        .to_vec(),
                    *image
                );
            }
        }
    }

    #[test]
    fn stored_noncanonical_bumps_fail_pool_account_authentication() {
        let program_id = Pubkey::new_unique();
        let (mut master, mut lanes, mut checkpoint, master_key) = fixtures(program_id);
        assert!(decode_master_account(&program_id, &master.info(), true).is_ok());
        master.data[7] ^= 1;
        assert!(decode_master_account(&program_id, &master.info(), true).is_err());
        master.data[7] ^= 1;
        for (lane_id, lane) in lanes.iter_mut().enumerate() {
            assert!(decode_lane_account(
                &program_id,
                &master_key,
                lane_id as u8,
                &lane.info(),
                false
            )
            .is_ok());
            lane.data[72] ^= 1;
            assert!(decode_lane_account(
                &program_id,
                &master_key,
                lane_id as u8,
                &lane.info(),
                false
            )
            .is_err());
            #[cfg(any(
                feature = "pair-forest-source-invariant-audit",
                feature = "pair-forest-deposit-invariant-audit"
            ))]
            assert!(decode_lane_account_from_program_invariant_v1(
                &program_id,
                &master_key,
                lane_id as u8,
                &lane.info(),
                false
            )
            .is_err());
            lane.data[72] ^= 1;
        }
        let plan = plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master.info(),
            &lanes.iter_mut().map(TestAccount::info).collect::<Vec<_>>(),
            &checkpoint.info(),
        )
        .unwrap();
        checkpoint.data = plan.checkpoint_image.to_vec();
        checkpoint.writable = false;
        assert!(decode_retained_pair_forest_checkpoint_account_v1(
            &program_id,
            &master_key,
            &checkpoint.info()
        )
        .is_ok());
        checkpoint.data[7] ^= 1;
        assert!(decode_retained_pair_forest_checkpoint_account_v1(
            &program_id,
            &master_key,
            &checkpoint.info()
        )
        .is_err());
    }

    #[test]
    fn stored_bump_authentication_rejects_every_wrong_bump_key_and_owner() {
        let program_id = Pubkey::new_unique();
        let (mut master, mut lanes, _checkpoint, master_key) = fixtures(program_id);
        let address_error: ProgramError = PoolV1ProgramError::InvalidPoolStateAddress.into();
        let state_error: ProgramError = PoolV1ProgramError::StateHistoryMismatch.into();
        let canonical_master_bump = master.data[7];
        for bump in 0..=u8::MAX {
            master.data[7] = bump;
            let result = decode_master_account(&program_id, &master.info(), true);
            if bump == canonical_master_bump {
                assert!(result.is_ok());
            } else {
                assert_eq!(
                    result.err(),
                    Some(address_error.clone()),
                    "master bump {bump}"
                );
            }
        }
        master.data[7] = canonical_master_bump;
        let master_image = master.data.clone();
        master.key = Pubkey::new_unique();
        assert_eq!(
            decode_master_account(&program_id, &master.info(), true).err(),
            Some(address_error.clone())
        );
        master.key = master_key;
        master.owner = Pubkey::new_unique();
        assert_eq!(
            decode_master_account(&program_id, &master.info(), true).err(),
            Some(ProgramError::IncorrectProgramId)
        );
        master.owner = program_id;
        assert_eq!(master.data, master_image);

        let lane_keys: Vec<Pubkey> = lanes.iter().map(|lane| lane.key).collect();
        for (lane_id, lane) in lanes.iter_mut().enumerate() {
            let lane_id = lane_id as u8;
            let canonical = lane.data[72];
            for bump in 0..=u8::MAX {
                lane.data[72] = bump;
                let strict =
                    decode_lane_account(&program_id, &master_key, lane_id, &lane.info(), false);
                #[cfg(any(
                    feature = "pair-forest-source-invariant-audit",
                    feature = "pair-forest-deposit-invariant-audit"
                ))]
                let invariant = decode_lane_account_from_program_invariant_v1(
                    &program_id,
                    &master_key,
                    lane_id,
                    &lane.info(),
                    false,
                );
                if bump == canonical {
                    assert!(strict.is_ok());
                    #[cfg(any(
                        feature = "pair-forest-source-invariant-audit",
                        feature = "pair-forest-deposit-invariant-audit"
                    ))]
                    assert!(invariant.is_ok());
                } else {
                    // Canonical key, wrong stored bump: the previous state
                    // error is kept after the fallback search.
                    assert_eq!(
                        strict.err(),
                        Some(state_error.clone()),
                        "lane {lane_id} bump {bump}"
                    );
                    #[cfg(any(
                        feature = "pair-forest-source-invariant-audit",
                        feature = "pair-forest-deposit-invariant-audit"
                    ))]
                    assert_eq!(
                        invariant.err(),
                        Some(state_error.clone()),
                        "lane {lane_id} bump {bump}"
                    );
                }
            }
            lane.data[72] = canonical;
            // Another lane's key, an arbitrary key and the master key are
            // address errors; so is the right image under the wrong lane id.
            let own_key = lane.key;
            for wrong in [
                lane_keys[(usize::from(lane_id) + 1) % 8],
                Pubkey::new_unique(),
                master_key,
            ] {
                lane.key = wrong;
                assert_eq!(
                    decode_lane_account(&program_id, &master_key, lane_id, &lane.info(), false)
                        .err(),
                    Some(address_error.clone())
                );
            }
            lane.key = own_key;
            assert_eq!(
                decode_lane_account(
                    &program_id,
                    &master_key,
                    (lane_id + 1) % 8,
                    &lane.info(),
                    false
                )
                .err(),
                Some(address_error.clone())
            );
            assert_eq!(
                decode_lane_account(&program_id, &master_key, 8, &lane.info(), false).err(),
                Some(ProgramError::InvalidSeeds)
            );
            lane.owner = Pubkey::new_unique();
            assert_eq!(
                decode_lane_account(&program_id, &master_key, lane_id, &lane.info(), false).err(),
                Some(ProgramError::IncorrectProgramId)
            );
            lane.owner = program_id;
            lane.signer = true;
            assert_eq!(
                decode_lane_account(&program_id, &master_key, lane_id, &lane.info(), false).err(),
                Some(address_error.clone())
            );
            lane.signer = false;
        }
    }

    /// Premise boundary, recorded as a test so that it cannot drift silently:
    /// a stored bump authenticates an existing account only because the Pool
    /// signs exclusively with canonical bumps. Natively, a Pool-owned image at
    /// a non-canonical off-curve PDA of the same seeds, storing that bump, is
    /// accepted. On chain no such account can exist: allocating or assigning
    /// it requires the Pool's `invoke_signed` with that bump.
    #[test]
    fn noncanonical_pda_with_matching_stored_bump_is_premise_bound() {
        let program_id = Pubkey::new_unique();
        let (_master, mut lanes, _checkpoint, master_key) = fixtures(program_id);
        let lane = &mut lanes[0];
        let canonical = lane.data[72];
        let (other_key, other_bump) = (0..canonical)
            .rev()
            .find_map(|bump| {
                Pubkey::create_program_address(
                    &[
                        POOL_V1_PAIR_FOREST_LANE_SEED,
                        master_key.as_ref(),
                        &[0],
                        &[bump],
                    ],
                    &program_id,
                )
                .ok()
                .map(|key| (key, bump))
            })
            .unwrap();
        lane.key = other_key;
        lane.data[72] = other_bump;
        assert!(decode_lane_account(&program_id, &master_key, 0, &lane.info(), false).is_ok());
        // The canonical search would have rejected it.
        assert_ne!(
            other_key,
            pool_v1_pair_forest_lane_address(&program_id, &master_key, 0)
                .unwrap()
                .0
        );
    }

    #[test]
    fn b4_noncanonical_checkpoint_and_page_with_matching_bump_are_premise_bound() {
        // Same recorded premise as the lane case above (F6): one
        // `create_program_address` does not establish canonicality; on chain
        // no Pool-owned checkpoint or page exists at a non-canonical bump
        // because the Pool creates both only at `find_program_address` bumps.
        let program_id = Pubkey::new_unique();
        let master_key = Pubkey::new_unique();
        let sequence = 3u64;
        let (canonical_key, canonical) =
            pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, sequence);
        let (other_key, other_bump) = (0..canonical)
            .rev()
            .find_map(|bump| {
                Pubkey::create_program_address(
                    &[
                        POOL_V1_PAIR_FOREST_CHECKPOINT_SEED,
                        master_key.as_ref(),
                        &sequence.to_le_bytes(),
                        &[bump],
                    ],
                    &program_id,
                )
                .ok()
                .map(|key| (key, bump))
            })
            .unwrap();
        assert_ne!(other_key, canonical_key);
        let checkpoint = PoolV1PairForestCheckpointV1 {
            bump: other_bump,
            master: master_key.to_bytes(),
            deployment_domain: [5; 32],
            checkpoint_sequence: sequence,
            global_root: digest(3),
            lane_sequences: [0; 8],
        };
        let mut account = TestAccount {
            key: other_key,
            owner: program_id,
            lamports: 1,
            data: encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint)
                .unwrap()
                .to_vec(),
            signer: false,
            writable: false,
            executable: false,
        };
        assert!(decode_retained_pair_forest_checkpoint_account_v1(
            &program_id,
            &master_key,
            &account.info()
        )
        .is_ok());

        let lane_key = Pubkey::new_unique();
        let (canonical_page, page_bump) = pool_v1_root_page_address(&program_id, &lane_key, 0);
        let (other_page, other_page_bump) = (0..page_bump)
            .rev()
            .find_map(|bump| {
                Pubkey::create_program_address(
                    &[
                        POOL_V1_ROOT_HISTORY_PAGE_SEED,
                        lane_key.as_ref(),
                        &0u64.to_le_bytes(),
                        &[bump],
                    ],
                    &program_id,
                )
                .ok()
                .map(|key| (key, bump))
            })
            .unwrap();
        assert_ne!(other_page, canonical_page);
        account.key = other_page;
        assert!(crate::history::require_root_page_address_with_bump(
            &program_id,
            &lane_key,
            0,
            other_page_bump,
            &account.info()
        )
        .is_ok());
    }

    #[test]
    fn vault_deposit_routes_one_occupied_empty_pair_and_creates_lane_history() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let (mut accounts, instruction, lane_id, commitment) =
            genesis_deposit_fixture(program_id, mint);
        let source_before = accounts[4].data.clone();
        let mut runtime = DepositCpi {
            apply_exact_delta: true,
            calls: 0,
        };
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        process_pair_forest_deposit_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut runtime,
        )
        .unwrap();
        drop(infos);
        assert_eq!(runtime.calls, 1);

        let lane =
            decode_pool_v1_pair_forest_lane_state_v1(&accounts[1].data, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap();
        assert_eq!(lane.lane_id, lane_id);
        assert_eq!(
            lane.bump,
            pool_v1_pair_forest_lane_address(&program_id, &accounts[0].key, lane_id)
                .unwrap()
                .1
        );
        assert_eq!(lane.tree.next_leaf_index, 1);
        let witness = PoolV1PairLeafWitnessV1::single_output(commitment).unwrap();
        assert_eq!(witness.second_occupied, M31::ZERO);
        assert_eq!(witness.second_commitment, [M31::ZERO; 8]);
        assert_eq!(witness.second_occupancy_inverse, M31::ZERO);
        let expected = canonical_genesis_lane(&program_id, &accounts[0].key, lane_id)
            .tree
            .append_one_with_empty_roots(witness.leaf_digest().unwrap(), &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        assert_eq!(lane.tree, expected);

        let page = validate_root_page_bytes(&accounts[2].data, &accounts[1].key, 0).unwrap();
        assert_eq!(page.filled, 2);
        assert_eq!(
            read_retained_root(&accounts[2].data, page, 0).unwrap(),
            POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH]
        );
        assert_eq!(
            read_retained_root(&accounts[2].data, page, 1).unwrap(),
            lane.tree.root
        );
        assert_eq!(
            u64::from_le_bytes(accounts[4].data[64..72].try_into().unwrap()),
            93
        );
        assert_eq!(
            u64::from_le_bytes(accounts[6].data[64..72].try_into().unwrap()),
            7
        );
        assert_ne!(accounts[4].data, source_before);

        // The next deposit uses the compact existing-page account shape and
        // appends without rewriting either retained root.
        accounts.truncate(FOREST_DEPOSIT_SAME_PAGE_ACCOUNT_COUNT);
        let first_page = accounts[2].data.clone();
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        process_pair_forest_deposit_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut runtime,
        )
        .unwrap();
        drop(infos);
        assert_eq!(runtime.calls, 2);
        let lane =
            decode_pool_v1_pair_forest_lane_state_v1(&accounts[1].data, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap();
        assert_eq!(lane.tree.next_leaf_index, 2);
        let page = validate_root_page_bytes(&accounts[2].data, &accounts[1].key, 0).unwrap();
        assert_eq!(page.filled, 3);
        assert_eq!(
            &accounts[2].data[64..64 + 2 * 32],
            &first_page[64..64 + 2 * 32]
        );
        assert_eq!(
            read_retained_root(&accounts[2].data, page, 2).unwrap(),
            lane.tree.root
        );
    }

    #[cfg(feature = "pair-forest-deposit-invariant-audit")]
    #[test]
    fn deposit_invariant_source_root_still_requires_exact_retained_history() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let (mut accounts, instruction, _, _) = genesis_deposit_fixture(program_id, mint);
        let mut runtime = DepositCpi {
            apply_exact_delta: true,
            calls: 0,
        };
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        process_pair_forest_deposit_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut runtime,
        )
        .unwrap();
        drop(infos);
        assert_eq!(runtime.calls, 1);

        accounts.truncate(FOREST_DEPOSIT_SAME_PAGE_ACCOUNT_COUNT);
        let root_start = POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES + 16;
        accounts[1].data[root_start..root_start + 32]
            .copy_from_slice(&encode_digest_canonical(&digest(92_000)));
        let lane_before = accounts[1].data.clone();
        let page_before = accounts[2].data.clone();
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        assert_eq!(
            process_pair_forest_deposit_with_runtime_v1(
                &program_id,
                &infos,
                &instruction,
                &Rent::default(),
                &mut runtime,
            ),
            Err(PoolV1ProgramError::StateHistoryMismatch.into())
        );
        drop(infos);
        assert_eq!(runtime.calls, 1, "history mismatch must precede token CPI");
        assert_eq!(accounts[1].data, lane_before);
        assert_eq!(accounts[2].data, page_before);
    }

    #[test]
    fn deposit_alias_or_bad_token_delta_fails_without_pool_writes() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let (mut bad_delta, instruction, _, _) = genesis_deposit_fixture(program_id, mint);
        let lane_before = bad_delta[1].data.clone();
        let page_before = bad_delta[2].data.clone();
        let infos: Vec<_> = bad_delta.iter_mut().map(TestAccount::info).collect();
        let mut runtime = DepositCpi {
            apply_exact_delta: false,
            calls: 0,
        };
        assert_eq!(
            process_pair_forest_deposit_with_runtime_v1(
                &program_id,
                &infos,
                &instruction,
                &Rent::default(),
                &mut runtime,
            ),
            Err(PoolV1ProgramError::TokenBalanceDeltaMismatch.into())
        );
        drop(infos);
        assert_eq!(runtime.calls, 1);
        assert_eq!(bad_delta[1].data, lane_before);
        assert_eq!(bad_delta[2].data, page_before);

        let (mut aliased, instruction, _, _) = genesis_deposit_fixture(program_id, mint);
        aliased[4].key = aliased[6].key;
        let lane_before = aliased[1].data.clone();
        let page_before = aliased[2].data.clone();
        let infos: Vec<_> = aliased.iter_mut().map(TestAccount::info).collect();
        let mut runtime = DepositCpi {
            apply_exact_delta: true,
            calls: 0,
        };
        assert_eq!(
            process_pair_forest_deposit_with_runtime_v1(
                &program_id,
                &infos,
                &instruction,
                &Rent::default(),
                &mut runtime,
            ),
            Err(ProgramError::InvalidArgument)
        );
        drop(infos);
        assert_eq!(runtime.calls, 0);
        assert_eq!(aliased[1].data, lane_before);
        assert_eq!(aliased[2].data, page_before);

        let (mut wrong_lane, instruction, lane_id, _) = genesis_deposit_fixture(program_id, mint);
        wrong_lane[1].key = pool_v1_pair_forest_lane_address(
            &program_id,
            &wrong_lane[0].key,
            lane_id.wrapping_add(1) & 7,
        )
        .unwrap()
        .0;
        let lane_before = wrong_lane[1].data.clone();
        let page_before = wrong_lane[2].data.clone();
        let infos: Vec<_> = wrong_lane.iter_mut().map(TestAccount::info).collect();
        let mut runtime = DepositCpi {
            apply_exact_delta: true,
            calls: 0,
        };
        assert!(process_pair_forest_deposit_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut runtime,
        )
        .is_err());
        drop(infos);
        assert_eq!(runtime.calls, 0);
        assert_eq!(wrong_lane[1].data, lane_before);
        assert_eq!(wrong_lane[2].data, page_before);
    }

    #[test]
    fn vault_deposit_rollover_preserves_full_history_and_starts_next_page() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let (mut accounts, instruction, lane_id, _) = genesis_deposit_fixture(program_id, mint);
        let mut lane = canonical_genesis_lane(&program_id, &accounts[0].key, lane_id);
        let mut roots = Vec::with_capacity(POOL_V1_ROOT_HISTORY_CAPACITY);
        roots.push(lane.tree.root);
        for index in 0..POOL_V1_ROOT_HISTORY_CAPACITY - 1 {
            let pair = PoolV1PairLeafWitnessV1::single_output(digest(20_000 + index as u32))
                .unwrap()
                .leaf_digest()
                .unwrap();
            lane.tree = lane
                .tree
                .append_one_with_empty_roots(pair, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap()
                .0;
            roots.push(lane.tree.root);
        }
        assert_eq!(lane.tree.next_leaf_index, 255);
        accounts[1].data =
            encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap()
                .to_vec();
        accounts[2].writable = false;
        let lane_key = accounts[1].key;
        write_new_page_unchecked(&mut accounts[2].data, &lane_key, 0, 0, &roots);
        let current_page_before = accounts[2].data.clone();
        accounts.insert(
            3,
            TestAccount {
                key: pool_v1_root_page_address(&program_id, &accounts[1].key, 1).0,
                owner: program_id,
                lamports: rent_lamports(POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES),
                data: vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            },
        );
        let mut runtime = DepositCpi {
            apply_exact_delta: true,
            calls: 0,
        };
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        process_pair_forest_deposit_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut runtime,
        )
        .unwrap();
        drop(infos);
        assert_eq!(runtime.calls, 1);
        assert_eq!(accounts[2].data, current_page_before);
        let lane =
            decode_pool_v1_pair_forest_lane_state_v1(&accounts[1].data, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap();
        assert_eq!(lane.tree.next_leaf_index, 256);
        let next_header = validate_root_page_bytes(&accounts[3].data, &accounts[1].key, 1).unwrap();
        assert_eq!(next_header.first_sequence, 256);
        assert_eq!(next_header.filled, 1);
        assert_eq!(
            read_retained_root(&accounts[3].data, next_header, 256).unwrap(),
            lane.tree.root
        );
    }

    #[test]
    fn initialize_rejects_underfunded_or_aliased_accounts_before_writes() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let instruction =
            encode_pair_forest_initialize_instruction_v1(&forest_initialization(mint)).unwrap();

        let mut underfunded = initialization_accounts(program_id, mint);
        underfunded[0].lamports =
            rent_lamports(POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES).saturating_sub(1);
        let infos: Vec<_> = underfunded.iter_mut().map(TestAccount::info).collect();
        assert!(process_pair_forest_initialize_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut NoCpi,
        )
        .is_err());
        drop(infos);
        assert!(underfunded[..9]
            .iter()
            .all(|account| account.data.iter().all(|byte| *byte == 0)));

        let mut aliased = initialization_accounts(program_id, mint);
        aliased[2].key = aliased[1].key;
        let infos: Vec<_> = aliased.iter_mut().map(TestAccount::info).collect();
        assert_eq!(
            process_pair_forest_initialize_with_runtime_v1(
                &program_id,
                &infos,
                &instruction,
                &Rent::default(),
                &mut NoCpi,
            ),
            Err(ProgramError::InvalidArgument)
        );
        drop(infos);
        assert!(aliased[..9]
            .iter()
            .all(|account| account.data.iter().all(|byte| *byte == 0)));
    }

    #[test]
    fn checkpoint_computes_root_writes_only_checkpoint_and_master_and_rejects_no_progress() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let initialization = forest_initialization(mint);
        let initialize_instruction =
            encode_pair_forest_initialize_instruction_v1(&initialization).unwrap();
        let mut initialized = initialization_accounts(program_id, mint);
        let infos: Vec<_> = initialized.iter_mut().map(TestAccount::info).collect();
        process_pair_forest_initialize_with_runtime_v1(
            &program_id,
            &infos,
            &initialize_instruction,
            &Rent::default(),
            &mut NoCpi,
        )
        .unwrap();
        drop(infos);

        let master_key = initialized[0].key;
        let checkpoint_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0).0;
        let mut checkpoint_accounts = initialized[..9].to_vec();
        for lane in &mut checkpoint_accounts[1..9] {
            lane.writable = false;
        }
        checkpoint_accounts.push(TestAccount {
            key: checkpoint_key,
            owner: program_id,
            lamports: rent_lamports(POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES),
            data: vec![0u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES],
            signer: false,
            writable: true,
            executable: false,
        });
        checkpoint_accounts.push(initialized[12].clone());
        checkpoint_accounts.push(initialized[13].clone());
        let lanes_before: [Vec<u8>; 8] =
            core::array::from_fn(|lane| checkpoint_accounts[1 + lane].data.clone());
        let instruction = encode_pair_forest_checkpoint_instruction_v1();
        let infos: Vec<_> = checkpoint_accounts
            .iter_mut()
            .map(TestAccount::info)
            .collect();
        process_pair_forest_checkpoint_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut NoCpi,
        )
        .unwrap();
        drop(infos);

        let master = decode_pool_v1_pair_forest_master_v1(&checkpoint_accounts[0].data).unwrap();
        assert!(master.has_checkpoint);
        assert_eq!(master.next_checkpoint_sequence, 1);
        let checkpoint =
            decode_pool_v1_pair_forest_checkpoint_v1(&checkpoint_accounts[9].data).unwrap();
        assert_eq!(checkpoint.master, master_key.to_bytes());
        assert_eq!(checkpoint.checkpoint_sequence, 0);
        assert_eq!(checkpoint.lane_sequences, [0u64; 8]);
        let roots = core::array::from_fn(|lane| {
            decode_pool_v1_pair_forest_lane_state_v1(
                &checkpoint_accounts[1 + lane].data,
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .unwrap()
            .tree
            .root
        });
        assert_eq!(
            checkpoint.global_root,
            pool_v1_pair_forest_global_root_v1(&roots)
        );
        for lane in 0..8 {
            assert_eq!(checkpoint_accounts[1 + lane].data, lanes_before[lane]);
        }

        let lane = 3usize;
        let mut advanced = decode_pool_v1_pair_forest_lane_state_v1(
            &checkpoint_accounts[1 + lane].data,
            &POOL_V1_PAIR_EMPTY_ROOTS,
        )
        .unwrap();
        advanced.tree = advanced
            .tree
            .append_one_with_empty_roots(digest(900), &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap()
            .0;
        checkpoint_accounts[1 + lane].data =
            encode_pool_v1_pair_forest_lane_state_v1(&advanced, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap()
                .to_vec();

        let next_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 1).0;
        checkpoint_accounts[9] = TestAccount {
            key: next_key,
            owner: program_id,
            lamports: rent_lamports(POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES),
            data: vec![0u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES],
            signer: false,
            writable: true,
            executable: false,
        };
        let infos: Vec<_> = checkpoint_accounts
            .iter_mut()
            .map(TestAccount::info)
            .collect();
        process_pair_forest_checkpoint_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut NoCpi,
        )
        .unwrap();
        drop(infos);
        let master = decode_pool_v1_pair_forest_master_v1(&checkpoint_accounts[0].data).unwrap();
        assert_eq!(master.next_checkpoint_sequence, 2);
        let checkpoint =
            decode_pool_v1_pair_forest_checkpoint_v1(&checkpoint_accounts[9].data).unwrap();
        assert_eq!(checkpoint.checkpoint_sequence, 1);
        assert_eq!(checkpoint.lane_sequences[lane], 1);

        let no_progress_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 2).0;
        checkpoint_accounts[9] = TestAccount {
            key: no_progress_key,
            owner: program_id,
            lamports: rent_lamports(POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES),
            data: vec![0u8; POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES],
            signer: false,
            writable: true,
            executable: false,
        };
        let master_before = checkpoint_accounts[0].data.clone();
        let infos: Vec<_> = checkpoint_accounts
            .iter_mut()
            .map(TestAccount::info)
            .collect();
        assert!(process_pair_forest_checkpoint_with_runtime_v1(
            &program_id,
            &infos,
            &instruction,
            &Rent::default(),
            &mut NoCpi,
        )
        .is_err());
        drop(infos);
        assert_eq!(checkpoint_accounts[0].data, master_before);
        assert!(checkpoint_accounts[9].data.iter().all(|byte| *byte == 0));
    }

    #[test]
    fn canonical_pdas_are_stable_distinct_and_lane_local_history_is_disjoint() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let master = pool_v1_pair_forest_master_address(&program_id, &mint).0;
        let mut seen = std::collections::HashSet::new();
        for lane in 0..8u8 {
            let address = pool_v1_pair_forest_lane_address(&program_id, &master, lane)
                .unwrap()
                .0;
            assert!(seen.insert(address));
            assert_eq!(
                pool_v1_pair_forest_lane_root_page_address(&program_id, &master, lane, 0)
                    .unwrap()
                    .0,
                pool_v1_root_page_address(&program_id, &address, 0).0
            );
        }
        assert_eq!(
            pool_v1_pair_forest_lane_address(&program_id, &master, 8),
            Err(ProgramError::InvalidSeeds)
        );
    }

    #[test]
    fn fixed_order_snapshot_plans_exact_images_without_mutation() {
        let program_id = Pubkey::new_unique();
        let (mut master, mut lanes, mut checkpoint, master_key) = fixtures(program_id);
        let master_before = master.data.clone();
        let lane_before: [Vec<u8>; 8] = core::array::from_fn(|lane| lanes[lane].data.clone());
        let checkpoint_before = checkpoint.data.clone();
        let master_info = master.info();
        let lane_infos: Vec<_> = lanes.iter_mut().map(TestAccount::info).collect();
        let checkpoint_info = checkpoint.info();
        let plan = plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master_info,
            &lane_infos,
            &checkpoint_info,
        )
        .unwrap();
        assert_eq!(plan.master, master_key);
        assert_eq!(plan.checkpoint, *checkpoint_info.key);
        assert_eq!(plan.lane_sequences, [0u64; 8]);
        assert_eq!(
            decode_pool_v1_pair_forest_checkpoint_v1(&plan.checkpoint_image)
                .unwrap()
                .global_root,
            pool_v1_pair_forest_global_root_v1(&core::array::from_fn(|_| {
                POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH]
            }))
        );
        drop((master_info, lane_infos, checkpoint_info));
        assert_eq!(master.data, master_before);
        assert_eq!(checkpoint.data, checkpoint_before);
        for lane in 0..8 {
            assert_eq!(lanes[lane].data, lane_before[lane]);
        }
    }

    #[test]
    fn swapped_aliased_writable_and_wrong_pda_lanes_fail_closed() {
        let program_id = Pubkey::new_unique();
        let (mut master, mut lanes, mut checkpoint, _) = fixtures(program_id);
        let master_info = master.info();
        let lane_infos: Vec<_> = lanes.iter_mut().map(TestAccount::info).collect();
        let checkpoint_info = checkpoint.info();

        let mut swapped = lane_infos.clone();
        swapped.swap(0, 1);
        assert!(plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master_info,
            &swapped,
            &checkpoint_info
        )
        .is_err());

        let mut aliased = lane_infos.clone();
        aliased[1] = aliased[0].clone();
        assert_eq!(
            plan_pair_forest_checkpoint_accounts_v1(
                &program_id,
                &master_info,
                &aliased,
                &checkpoint_info
            ),
            Err(ProgramError::InvalidArgument)
        );

        let mut writable = lane_infos.clone();
        writable[0].is_writable = true;
        assert!(plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master_info,
            &writable,
            &checkpoint_info
        )
        .is_err());

        let mut wrong_pda = lane_infos.clone();
        let wrong_key = Pubkey::new_unique();
        wrong_pda[0].key = &wrong_key;
        assert!(plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master_info,
            &wrong_pda,
            &checkpoint_info
        )
        .is_err());
    }

    #[test]
    fn occupied_checkpoint_and_wrong_master_fail_before_any_write() {
        let program_id = Pubkey::new_unique();
        let (mut master, mut lanes, mut checkpoint, _) = fixtures(program_id);
        checkpoint.data[0] = 1;
        let before = checkpoint.data.clone();
        let master_info = master.info();
        let lane_infos: Vec<_> = lanes.iter_mut().map(TestAccount::info).collect();
        let checkpoint_info = checkpoint.info();
        assert!(plan_pair_forest_checkpoint_accounts_v1(
            &program_id,
            &master_info,
            &lane_infos,
            &checkpoint_info
        )
        .is_err());
        drop((master_info, lane_infos, checkpoint_info));
        assert_eq!(checkpoint.data, before);
    }

    #[test]
    fn terminal_marker_creation_fails_closed_rolls_back_and_rejects_replay() {
        let program_id = Pubkey::new_unique();
        let rent = Rent::default();

        // Payer authentication is not implied by its position in the account
        // list: it must be a writable System-owned signer.
        {
            let (mut accounts, instruction, _) =
                system_marker_terminal_transfer_fixture(program_id);
            accounts[5].signer = false;
            let before = accounts
                .iter()
                .map(|account| (account.owner, account.lamports, account.data.clone()))
                .collect::<Vec<_>>();
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            assert_eq!(
                process_pair_forest_terminal_with_verifier_v1(
                    &program_id,
                    &infos,
                    &instruction,
                    1,
                    &rent,
                    &mut NoCpi,
                    |_, _, _, _, _, _, _, _, _, _, _| panic!("unsigned payer reached verifier"),
                    |_| {},
                ),
                Err(PoolV1ProgramError::InvalidPayer.into()),
            );
            drop(infos);
            assert_eq!(
                accounts
                    .iter()
                    .map(|account| (account.owner, account.lamports, account.data.clone()))
                    .collect::<Vec<_>>(),
                before,
            );
        }

        // A lookalike account at the System Program address but under the
        // wrong loader is rejected before marker allocation or verification.
        {
            let (mut accounts, instruction, _) =
                system_marker_terminal_transfer_fixture(program_id);
            accounts[6].owner = Pubkey::new_unique();
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            assert_eq!(
                process_pair_forest_terminal_with_verifier_v1(
                    &program_id,
                    &infos,
                    &instruction,
                    1,
                    &rent,
                    &mut NoCpi,
                    |_, _, _, _, _, _, _, _, _, _, _| panic!(
                        "spoofed System Program reached verifier"
                    ),
                    |_| {},
                ),
                Err(PoolV1ProgramError::InvalidSystemProgram.into()),
            );
        }

        // The writable marker must be the exact PDA for this Pool and
        // canonical nullifier; an arbitrary fresh writable account is not a
        // substitute.
        {
            let (mut accounts, instruction, _) =
                system_marker_terminal_transfer_fixture(program_id);
            accounts[4].key = Pubkey::new_unique();
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            assert_eq!(
                process_pair_forest_terminal_with_verifier_v1(
                    &program_id,
                    &infos,
                    &instruction,
                    1,
                    &rent,
                    &mut NoCpi,
                    |_, _, _, _, _, _, _, _, _, _, _| panic!("wrong marker reached verifier"),
                    |_| {},
                ),
                Err(PoolV1ProgramError::InvalidNullifierMarkerAddress.into()),
            );
        }

        // A pre-existing Pool-owned marker is accepted only at the exact size
        // and all-zero state. Malformed nonzero bytes are never overwritten.
        {
            let (mut accounts, instruction, _) =
                system_marker_terminal_transfer_fixture(program_id);
            accounts[4].owner = program_id;
            accounts[4].lamports = rent_lamports(POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES);
            accounts[4].data = vec![0u8; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
            accounts[4].data[0] = 1;
            let before = accounts[4].data.clone();
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            assert_eq!(
                process_pair_forest_terminal_with_verifier_v1(
                    &program_id,
                    &infos,
                    &instruction,
                    1,
                    &rent,
                    &mut NoCpi,
                    |_, _, _, _, _, _, _, _, _, _, _| panic!("malformed marker reached verifier"),
                    |_| {},
                ),
                Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into()),
            );
            drop(infos);
            assert_eq!(accounts[4].data, before);
        }

        // The System CPI propagates insufficient payer funds before verifier
        // execution, leaving the fresh marker and Pool state untouched.
        {
            let (mut accounts, instruction, _) =
                system_marker_terminal_transfer_fixture(program_id);
            accounts[5].lamports = 0;
            let before = accounts
                .iter()
                .map(|account| (account.owner, account.lamports, account.data.clone()))
                .collect::<Vec<_>>();
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            let mut runtime = MarkerSystemCpi {
                pool_program: program_id,
                calls: 0,
            };
            assert_eq!(
                process_pair_forest_terminal_with_verifier_v1(
                    &program_id,
                    &infos,
                    &instruction,
                    1,
                    &rent,
                    &mut runtime,
                    |_, _, _, _, _, _, _, _, _, _, _| panic!("unfunded marker reached verifier"),
                    |_| {},
                ),
                Err(ProgramError::InsufficientFunds),
            );
            drop(infos);
            assert_eq!(runtime.calls, 1);
            assert_eq!(
                accounts
                    .iter()
                    .map(|account| (account.owner, account.lamports, account.data.clone()))
                    .collect::<Vec<_>>(),
                before,
            );
        }

        // Marker creation deliberately precedes verifier CPI. The host mock
        // exposes the intermediate created account; the rollback block models
        // Solana's instruction journal and confirms the complete original
        // account images are restored when the verifier fails.
        {
            let (mut accounts, instruction, _) =
                system_marker_terminal_transfer_fixture(program_id);
            let before = accounts
                .iter()
                .map(|account| (account.owner, account.lamports, account.data.clone()))
                .collect::<Vec<_>>();
            let payer_before = accounts[5].lamports;
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            let mut runtime = MarkerSystemCpi {
                pool_program: program_id,
                calls: 0,
            };
            let verifier_error = ProgramError::Custom(0xfeed_0073);
            assert_eq!(
                process_pair_forest_terminal_with_verifier_v1(
                    &program_id,
                    &infos,
                    &instruction,
                    1,
                    &rent,
                    &mut runtime,
                    |_, _, _, _, _, _, _, _, _, _, _| Err(verifier_error.clone()),
                    |_| {},
                ),
                Err(verifier_error),
            );
            assert_eq!(runtime.calls, 1);
            assert_eq!(*infos[4].owner, program_id);
            assert_eq!(infos[4].data_len(), POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES);
            assert!(infos[4]
                .try_borrow_data()
                .unwrap()
                .iter()
                .all(|byte| *byte == 0));
            assert!(rent.is_exempt(infos[4].lamports(), infos[4].data_len()));
            drop(infos);
            assert_eq!(accounts[2].data, before[2].2);
            assert_eq!(accounts[3].data, before[3].2);

            // Host-only transaction-journal rollback for the System CPI. A
            // validator/LiteSVM replay remains the runtime release gate.
            accounts[4].owner = before[4].0;
            accounts[4].lamports = before[4].1;
            accounts[4].data.clone_from(&before[4].2);
            accounts[5].lamports = payer_before;
            assert_eq!(
                accounts
                    .iter()
                    .map(|account| (account.owner, account.lamports, account.data.clone()))
                    .collect::<Vec<_>>(),
                before,
            );
        }

        // A successful terminal also tolerates a griefing lamport sent to the
        // otherwise-empty PDA: it tops up, allocates and assigns the account,
        // then consumes the marker in this same instruction. The exact same
        // request rejects before another System CPI or verifier call.
        {
            let (mut accounts, instruction, result) =
                system_marker_terminal_transfer_fixture(program_id);
            accounts[4].lamports = 1;
            let payer_and_marker_lamports = accounts[4].lamports + accounts[5].lamports;
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            let mut runtime = MarkerSystemCpi {
                pool_program: program_id,
                calls: 0,
            };
            process_pair_forest_terminal_with_verifier_v1(
                &program_id,
                &infos,
                &instruction,
                1,
                &rent,
                &mut runtime,
                |_, _, _, _, _, _, _, _, _, _, _| {
                    Ok(AuthenticatedPairForestResultV1::for_test(result))
                },
                |_| {},
            )
            .unwrap();
            assert_eq!(runtime.calls, 3);
            assert_eq!(*infos[4].owner, program_id);
            assert_eq!(
                infos[4].lamports() + infos[5].lamports(),
                payer_and_marker_lamports
            );
            let decoded_marker = aspis_statement::pool_v1::decode_pool_v1_nullifier_marker(
                &infos[4].try_borrow_data().unwrap(),
            )
            .unwrap();
            assert_eq!(decoded_marker.nullifier, result.nullifier);
            let before_replay = infos
                .iter()
                .map(|account| account.try_borrow_data().unwrap().to_vec())
                .collect::<Vec<_>>();
            assert_eq!(
                process_pair_forest_terminal_with_verifier_v1(
                    &program_id,
                    &infos,
                    &instruction,
                    2,
                    &rent,
                    &mut runtime,
                    |_, _, _, _, _, _, _, _, _, _, _| panic!("replay reached verifier"),
                    |_| {},
                ),
                Err(PoolV1ProgramError::NullifierAlreadyConsumed.into()),
            );
            assert_eq!(runtime.calls, 3);
            assert_eq!(
                infos
                    .iter()
                    .map(|account| account.try_borrow_data().unwrap().to_vec())
                    .collect::<Vec<_>>(),
                before_replay,
            );
        }
    }


    /// Run the terminal with no CPI and a verifier that must not be reached.
    fn reject_before_cpi(
        program_id: &Pubkey,
        accounts: &mut [TestAccount],
        instruction: &[u8],
    ) -> ProgramResult {
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        process_pair_forest_terminal_with_verifier_v1(
            program_id,
            &infos,
            instruction,
            1,
            &Rent::default(),
            &mut NoCpi,
            |_, _, _, _, _, _, _, _, _, _, _| panic!("rejected input reached verifier"),
            |_| {},
        )
    }

    #[test]
    fn b1_marker_is_created_with_seed_once_and_replay_is_already_consumed() {
        let program_id = Pubkey::new_unique();
        let rent = Rent::default();
        // (prefund lamports, expected System CPI count): none -> one
        // CreateAccountWithSeed; partial -> Transfer + AllocateWithSeed +
        // AssignWithSeed; full rent -> AllocateWithSeed + AssignWithSeed.
        for (prefund, expected_calls) in [
            (0u64, 1usize),
            (1, 3),
            (rent_lamports(POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES), 2),
        ] {
            let (mut accounts, instruction, result) =
                system_marker_terminal_transfer_fixture(program_id);
            let (expected_key, _) = crate::pool_v1_pair_forest_nullifier_marker_address(
                &program_id,
                &accounts[0].key,
                &aspis_statement::encode_digest_canonical(&result.nullifier),
            )
            .unwrap();
            assert_eq!(accounts[4].key, expected_key);
            accounts[4].lamports = prefund;
            let total = accounts[4].lamports + accounts[5].lamports;
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            let mut runtime = MarkerSystemCpi {
                pool_program: program_id,
                calls: 0,
            };
            process_pair_forest_terminal_with_verifier_v1(
                &program_id,
                &infos,
                &instruction,
                1,
                &rent,
                &mut runtime,
                |_, _, _, _, _, _, _, _, _, _, _| {
                    Ok(AuthenticatedPairForestResultV1::for_test(result))
                },
                |_| {},
            )
            .unwrap();
            assert_eq!(runtime.calls, expected_calls, "prefund {prefund}");
            assert_eq!(*infos[4].owner, program_id);
            assert_eq!(infos[4].lamports() + infos[5].lamports(), total);
            assert!(rent.is_exempt(infos[4].lamports(), infos[4].data_len()));
            let decoded = aspis_statement::pool_v1::decode_pool_v1_nullifier_marker(
                &infos[4].try_borrow_data().unwrap(),
            )
            .unwrap();
            assert_eq!(decoded.nullifier, result.nullifier);
            // Second spend of the same note: rejected as already consumed,
            // before any CPI or verifier call, with every byte unchanged.
            let before = infos
                .iter()
                .map(|account| account.try_borrow_data().unwrap().to_vec())
                .collect::<Vec<_>>();
            assert_eq!(
                process_pair_forest_terminal_with_verifier_v1(
                    &program_id,
                    &infos,
                    &instruction,
                    2,
                    &rent,
                    &mut runtime,
                    |_, _, _, _, _, _, _, _, _, _, _| panic!("replay reached verifier"),
                    |_| {},
                ),
                Err(PoolV1ProgramError::NullifierAlreadyConsumed.into()),
            );
            assert_eq!(runtime.calls, expected_calls);
            assert_eq!(
                infos
                    .iter()
                    .map(|account| account.try_borrow_data().unwrap().to_vec())
                    .collect::<Vec<_>>(),
                before
            );
        }
    }

    #[test]
    fn b1_b4_terminal_mutations_fail_closed_before_cpi() {
        let program_id = Pubkey::new_unique();
        let (fixture, instruction, result) = system_marker_terminal_transfer_fixture(program_id);
        let master_key = fixture[0].key;
        let nullifier = aspis_statement::encode_digest_canonical(&result.nullifier);
        let (_, seed) =
            crate::pool_v1_pair_forest_nullifier_marker_address(&program_id, &master_key, &nullifier)
                .unwrap();
        let seed_text = core::str::from_utf8(&seed).unwrap();
        let mut other_seed = seed;
        other_seed[0] ^= 1;
        let mut count = 0usize;

        // Marker: wrong authority (base), wrong seed, wrong derivation owner,
        // the legacy PDA address; each forged as a Pool-owned zeroed account
        // (which the Pool would otherwise populate without a System CPI).
        for key in [
            Pubkey::create_with_seed(&Pubkey::new_unique(), seed_text, &program_id).unwrap(),
            Pubkey::create_with_seed(&fixture[2].key, seed_text, &program_id).unwrap(),
            Pubkey::create_with_seed(
                &master_key,
                core::str::from_utf8(&other_seed).unwrap(),
                &program_id,
            )
            .unwrap(),
            Pubkey::create_with_seed(&master_key, seed_text, &Pubkey::new_unique()).unwrap(),
            crate::pool_v1_nullifier_marker_address(&program_id, &master_key, &nullifier)
                .unwrap()
                .0,
        ] {
            let mut accounts = fixture.clone();
            accounts[4].key = key;
            accounts[4].owner = program_id;
            accounts[4].lamports = rent_lamports(POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES);
            accounts[4].data = vec![0; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
            assert_eq!(
                reject_before_cpi(&program_id, &mut accounts, &instruction),
                Err(PoolV1ProgramError::InvalidNullifierMarkerAddress.into())
            );
            count += 1;
        }
        // Marker at the right address but prefunded and owned by someone else,
        // or with signer / read-only privileges.
        for mutate in 0..3 {
            let mut accounts = fixture.clone();
            match mutate {
                0 => {
                    accounts[4].owner = Pubkey::new_unique();
                    accounts[4].lamports = 1;
                    accounts[4].data = vec![0; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES];
                }
                1 => accounts[4].signer = true,
                _ => accounts[4].writable = false,
            }
            let error = reject_before_cpi(&program_id, &mut accounts, &instruction);
            assert!(
                error == Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into())
                    || (mutate != 0 && error.is_err()),
                "mutation {mutate}: {error:?}"
            );
            count += 1;
        }
        // Master (marker authority): wrong owner or signer flag.
        {
            let mut accounts = fixture.clone();
            accounts[0].owner = Pubkey::new_unique();
            assert_eq!(
                reject_before_cpi(&program_id, &mut accounts, &instruction),
                Err(ProgramError::IncorrectProgramId)
            );
            let mut accounts = fixture.clone();
            accounts[0].signer = true;
            assert_eq!(
                reject_before_cpi(&program_id, &mut accounts, &instruction),
                Err(ProgramError::InvalidAccountData)
            );
            // Payer must sign.
            let mut accounts = fixture.clone();
            accounts[5].signer = false;
            assert_eq!(
                reject_before_cpi(&program_id, &mut accounts, &instruction),
                Err(PoolV1ProgramError::InvalidPayer.into())
            );
            count += 3;
        }
        // Checkpoint: every wrong stored bump (byte 7).
        let canonical_checkpoint = fixture[1].data[7];
        for bump in 0..=255u8 {
            if bump == canonical_checkpoint {
                continue;
            }
            let mut accounts = fixture.clone();
            accounts[1].data[7] = bump;
            assert_eq!(
                reject_before_cpi(&program_id, &mut accounts, &instruction),
                Err(PoolV1ProgramError::StateHistoryMismatch.into()),
                "checkpoint bump {bump}"
            );
            count += 1;
        }
        // Current page (genesis): every wrong hint byte.
        let hint_start = instruction.len() - POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES;
        let canonical_page = instruction[hint_start];
        for bump in 0..=255u8 {
            if bump == canonical_page {
                continue;
            }
            let mut accounts = fixture.clone();
            let mut data = instruction.clone();
            data[hint_start] = bump;
            assert_eq!(
                reject_before_cpi(&program_id, &mut accounts, &data),
                Err(PoolV1ProgramError::InvalidRootPageAddress.into()),
                "page bump {bump}"
            );
            count += 1;
        }
        // Unused hint bytes must be zero; the old (hint-free) length and a
        // longer suffix are malformed instruction data.
        for (offset, value) in [(1usize, 1u8), (2, 255), (3, 254)] {
            let mut accounts = fixture.clone();
            let mut data = instruction.clone();
            data[hint_start + offset] = value;
            assert_eq!(
                reject_before_cpi(&program_id, &mut accounts, &data),
                Err(ProgramError::InvalidInstructionData)
            );
            count += 1;
        }
        for data in [
            instruction[..hint_start].to_vec(),
            [instruction.as_slice(), &[0u8]].concat(),
            instruction[..instruction.len() - 1].to_vec(),
        ] {
            let mut accounts = fixture.clone();
            assert_eq!(
                reject_before_cpi(&program_id, &mut accounts, &data),
                Err(ProgramError::InvalidInstructionData)
            );
            count += 1;
        }
        assert_eq!(count, 5 + 3 + 3 + 255 + 255 + 3 + 3);
    }

    #[test]
    fn b4_page_hints_reject_every_wrong_bump_for_same_page_and_rollover() {
        let program_id = Pubkey::new_unique();
        for page_kind in [1u8, 2] {
            let (mut accounts, _, _) = system_marker_terminal_transfer_fixture(program_id);
            let mut lane = decode_pool_v1_pair_forest_lane_state_v1(
                &accounts[2].data,
                &POOL_V1_PAIR_EMPTY_ROOTS,
            )
            .unwrap();
            let lane_key = accounts[2].key;
            lane.tree.next_leaf_index = if page_kind == 1 { 1 } else { 255 };
            let roots = vec![lane.tree.root; lane.tree.next_leaf_index as usize + 1];
            write_new_page_unchecked(&mut accounts[3].data, &lane_key, 0, 0, &roots);
            if page_kind == 2 {
                accounts[3].writable = false;
                accounts.insert(
                    4,
                    TestAccount {
                        key: pool_v1_root_page_address(&program_id, &lane_key, 1).0,
                        owner: program_id,
                        lamports: 1,
                        data: vec![0; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
                        signer: false,
                        writable: true,
                        executable: false,
                    },
                );
            }
            let hints = pool_v1_pair_forest_terminal_bump_hints_v1(
                &program_id,
                &accounts[0].key,
                &lane_key,
                lane.tree.next_leaf_index,
                false,
            );
            assert_eq!(hints.next_page != 0, page_kind == 2);
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            assert!(
                plan_pair_forest_spend_layout_v1(&program_id, &infos, &lane, false, hints).is_ok()
            );
            let mut rejected = 0;
            for bump in 0..=255u8 {
                if bump != hints.current_page {
                    let wrong = PoolV1PairForestTerminalBumpHintsV1 {
                        current_page: bump,
                        ..hints
                    };
                    assert_eq!(
                        plan_pair_forest_spend_layout_v1(&program_id, &infos, &lane, false, wrong)
                            .err(),
                        Some(PoolV1ProgramError::InvalidRootPageAddress.into())
                    );
                    rejected += 1;
                }
                if page_kind == 2 && bump != hints.next_page {
                    let wrong = PoolV1PairForestTerminalBumpHintsV1 {
                        next_page: bump,
                        ..hints
                    };
                    assert_eq!(
                        plan_pair_forest_spend_layout_v1(&program_id, &infos, &lane, false, wrong)
                            .err(),
                        Some(PoolV1ProgramError::InvalidRootPageAddress.into())
                    );
                    rejected += 1;
                }
            }
            assert_eq!(rejected, if page_kind == 2 { 510 } else { 255 });
            if page_kind == 1 {
                let stray = PoolV1PairForestTerminalBumpHintsV1 {
                    next_page: 7,
                    ..hints
                };
                assert_eq!(
                    plan_pair_forest_spend_layout_v1(&program_id, &infos, &lane, false, stray)
                        .err(),
                    Some(ProgramError::InvalidInstructionData)
                );
            }
        }
    }

    #[test]
    fn one_terminal_transfer_updates_only_selected_lane_history_and_marker() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let (master_key, mut master_state) = master(program_id, mint);
        master_state.identity.token_program = LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes();
        master_state.has_checkpoint = true;
        master_state.next_checkpoint_sequence = 1;
        let nullifier = digest(1);
        let lane_id =
            aspis_statement::pool_v1::pool_v1_pair_forest_output_lane_v1(&nullifier).unwrap();
        let lane_key = pool_v1_pair_forest_lane_address(&program_id, &master_key, lane_id)
            .unwrap()
            .0;
        let lane = canonical_genesis_lane(&program_id, &master_key, lane_id);
        let (next_tree, _) = lane
            .tree
            .append_one_with_empty_roots(digest(9_000), &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap();
        let checkpoint = PoolV1PairForestCheckpointV1 {
            bump: pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0).1,
            master: master_key.to_bytes(),
            deployment_domain: master_state.identity.deployment_domain,
            checkpoint_sequence: 0,
            global_root: digest(7_000),
            lane_sequences: [0; 8],
        };
        let checkpoint_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0).0;
        let request = PoolV1PairForestTerminalRequestV1 {
            verifier_profile: [31; 32],
            verifier_release: [32; 32],
            pool_program: program_id.to_bytes(),
            public: PoolV1PairForestTerminalPaymentV1::PrivateTransfer(
                PoolV1PrivateTransferPublicV1 {
                    pool: master_key.to_bytes(),
                    deployment_domain: master_state.identity.deployment_domain,
                    anchor_sequence: 0,
                    anchor_root: checkpoint.global_root,
                    nullifier,
                    asset_id: master_state.identity.asset_id,
                    recipient_commitment: digest(100),
                    change_commitment: digest(200),
                },
            ),
        };
        let instruction = terminal_instruction(&program_id, &request, &lane_key, 0);
        let result = PoolV1PairForestTerminalResultV1 {
            transition_kind: PoolV1TransitionKind::PrivateTransfer,
            master_account: master_key.to_bytes(),
            selected_lane_account: lane_key.to_bytes(),
            output_lane: lane_id,
            nullifier,
            verified_afterstate: PoolV1PairVerifiedAfterstateV1 {
                next_pair_index: next_tree.next_leaf_index,
                next_root: next_tree.root,
                next_frontier: next_tree.frontier,
            },
        };
        let marker_key = crate::pool_v1_pair_forest_nullifier_marker_address(
            &program_id,
            &master_key,
            &aspis_statement::encode_digest_canonical(&nullifier),
        )
        .unwrap()
        .0;
        let page_key =
            pool_v1_pair_forest_lane_root_page_address(&program_id, &master_key, lane_id, 0)
                .unwrap()
                .0;
        let mut accounts = vec![
            TestAccount {
                key: master_key,
                owner: program_id,
                lamports: 1,
                data: encode_pool_v1_pair_forest_master_v1(&master_state)
                    .unwrap()
                    .to_vec(),
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: checkpoint_key,
                owner: program_id,
                lamports: 1,
                data: encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint)
                    .unwrap()
                    .to_vec(),
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: lane_key,
                owner: program_id,
                lamports: 1,
                data: encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS)
                    .unwrap()
                    .to_vec(),
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: page_key,
                owner: program_id,
                lamports: 1,
                data: vec![0; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: marker_key,
                owner: program_id,
                lamports: rent_lamports(POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES),
                data: vec![0; POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES],
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: system_program::id(),
                lamports: 10 * rent_lamports(POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES),
                data: vec![],
                signer: true,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: system_program::id(),
                owner: native_loader::id(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: true,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: Pubkey::new_unique(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: Pubkey::new_unique(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: bpf_loader::id(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: true,
            },
            TestAccount {
                key: Pubkey::new_unique(),
                owner: Pubkey::new_unique(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
        ];
        append_test_verifier_checkpoint(&mut accounts);
        let mut bad_requests = Vec::new();
        let mut wrong = request;
        wrong.pool_program[0] ^= 1;
        bad_requests.push(wrong);
        let mut wrong = request;
        if let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) = &mut wrong.public {
            public.pool[0] ^= 1;
        }
        bad_requests.push(wrong);
        let mut wrong = request;
        if let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) = &mut wrong.public {
            public.deployment_domain[0] ^= 1;
        }
        bad_requests.push(wrong);
        let mut wrong = request;
        if let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) = &mut wrong.public {
            public.anchor_root[0] = public.anchor_root[0].add(M31::ONE);
        }
        bad_requests.push(wrong);
        let mut wrong = request;
        if let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) = &mut wrong.public {
            public.asset_id = public.asset_id.add(M31::ONE);
        }
        bad_requests.push(wrong);
        for bad in bad_requests {
            let bad_instruction = terminal_instruction(&program_id, &bad, &lane_key, 0);
            let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
            assert!(process_pair_forest_terminal_with_verifier_v1(
                &program_id,
                &infos,
                &bad_instruction,
                1,
                &Rent::default(),
                &mut NoCpi,
                |_, _, _, _, _, _, _, _, _, _, _| panic!("bad request reached verifier"),
                |_| {},
            )
            .is_err());
        }
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        let mut no_cpi = NoCpi;
        process_pair_forest_terminal_with_verifier_v1(
            &program_id,
            &infos,
            &instruction,
            1,
            &Rent::default(),
            &mut no_cpi,
            |_, _, _, _, _, _, _, _, _, got, _| {
                assert_eq!(got, &request);
                Ok(AuthenticatedPairForestResultV1::for_test(result))
            },
            |_| {},
        )
        .unwrap();
        drop(infos);
        let written_lane =
            decode_pool_v1_pair_forest_lane_state_v1(&accounts[2].data, &POOL_V1_PAIR_EMPTY_ROOTS)
                .unwrap();
        assert_eq!(written_lane.tree, next_tree);
        assert_eq!(written_lane.bump, lane.bump);
        assert!(accounts[4].data.iter().any(|byte| *byte != 0));
        assert_eq!(
            decode_pool_v1_pair_forest_master_v1(&accounts[0].data).unwrap(),
            master_state
        );

        let before = accounts
            .iter()
            .map(|account| account.data.clone())
            .collect::<Vec<_>>();
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        assert!(process_pair_forest_terminal_with_verifier_v1(
            &program_id,
            &infos,
            &instruction,
            2,
            &Rent::default(),
            &mut no_cpi,
            |_, _, _, _, _, _, _, _, _, _, _| panic!("stale replay reached verifier"),
            |_| {},
        )
        .is_err());
        drop(infos);
        assert_eq!(
            accounts
                .iter()
                .map(|account| account.data.clone())
                .collect::<Vec<_>>(),
            before
        );
    }

    #[test]
    fn one_terminal_withdrawal_authenticates_loader_and_checks_custody_delta_before_writes() {
        let program_id = Pubkey::new_unique();
        let mint = Pubkey::new_unique();
        let (master_key, mut master_state) = master(program_id, mint);
        master_state.identity.asset_mint = mint.to_bytes();
        master_state.identity.token_program = LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes();
        master_state.has_checkpoint = true;
        master_state.next_checkpoint_sequence = 1;
        let nullifier = digest(2);
        let lane_id =
            aspis_statement::pool_v1::pool_v1_pair_forest_output_lane_v1(&nullifier).unwrap();
        let lane_key = pool_v1_pair_forest_lane_address(&program_id, &master_key, lane_id)
            .unwrap()
            .0;
        let lane = canonical_genesis_lane(&program_id, &master_key, lane_id);
        let (next_tree, _) = lane
            .tree
            .append_one_with_empty_roots(digest(9_100), &POOL_V1_PAIR_EMPTY_ROOTS)
            .unwrap();
        let checkpoint = PoolV1PairForestCheckpointV1 {
            bump: pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0).1,
            master: master_key.to_bytes(),
            deployment_domain: master_state.identity.deployment_domain,
            checkpoint_sequence: 0,
            global_root: digest(7_100),
            lane_sequences: [0; 8],
        };
        let checkpoint_key = pool_v1_pair_forest_checkpoint_address(&program_id, &master_key, 0).0;
        let destination = Pubkey::new_unique();
        let request = PoolV1PairForestTerminalRequestV1 {
            verifier_profile: [41; 32],
            verifier_release: [42; 32],
            pool_program: program_id.to_bytes(),
            public: PoolV1PairForestTerminalPaymentV1::Withdrawal(PoolV1WithdrawalPublicV1 {
                pool: master_key.to_bytes(),
                deployment_domain: master_state.identity.deployment_domain,
                anchor_sequence: 0,
                anchor_root: checkpoint.global_root,
                nullifier,
                asset_id: master_state.identity.asset_id,
                amount: 25,
                destination_token_account: destination.to_bytes(),
                change_commitment: digest(300),
            }),
        };
        let result = PoolV1PairForestTerminalResultV1 {
            transition_kind: PoolV1TransitionKind::Withdrawal,
            master_account: master_key.to_bytes(),
            selected_lane_account: lane_key.to_bytes(),
            output_lane: lane_id,
            nullifier,
            verified_afterstate: PoolV1PairVerifiedAfterstateV1 {
                next_pair_index: next_tree.next_leaf_index,
                next_root: next_tree.root,
                next_frontier: next_tree.frontier,
            },
        };
        let marker_key = crate::pool_v1_pair_forest_nullifier_marker_address(
            &program_id,
            &master_key,
            &aspis_statement::encode_digest_canonical(&nullifier),
        )
        .unwrap()
        .0;
        let mut accounts = terminal_base_accounts(
            program_id,
            master_key,
            &master_state,
            checkpoint_key,
            &checkpoint,
            lane_key,
            &lane,
            marker_key,
        );
        let authority = crate::pool_v1_vault_authority_address(&program_id, &master_key).0;
        accounts.extend([
            TestAccount {
                key: mint,
                owner: LEGACY_SPL_TOKEN_PROGRAM_ID,
                lamports: 1,
                data: initialized_mint_data(),
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: crate::pool_v1_vault_token_account_address(&program_id, &master_key).0,
                owner: LEGACY_SPL_TOKEN_PROGRAM_ID,
                lamports: 1,
                data: initialized_token_data(mint, authority, 100),
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: destination,
                owner: LEGACY_SPL_TOKEN_PROGRAM_ID,
                lamports: 1,
                data: initialized_token_data(mint, Pubkey::new_unique(), 10),
                signer: false,
                writable: true,
                executable: false,
            },
            TestAccount {
                key: authority,
                owner: system_program::id(),
                lamports: 0,
                data: vec![],
                signer: false,
                writable: false,
                executable: false,
            },
            TestAccount {
                key: LEGACY_SPL_TOKEN_PROGRAM_ID,
                owner: bpf_loader::id(),
                lamports: 1,
                data: vec![],
                signer: false,
                writable: false,
                executable: true,
            },
        ]);
        let instruction = terminal_instruction(&program_id, &request, &lane_key, 0);

        // The fixed token-program address and executable bit are insufficient:
        // authenticate that the program is itself owned by a supported loader,
        // and reject before either verifier execution or custody CPI.
        let token_program_index = accounts.len() - 1;
        append_test_verifier_checkpoint(&mut accounts);
        accounts[token_program_index].owner = native_loader::id();
        let invalid_loader_before = accounts
            .iter()
            .map(|account| account.data.clone())
            .collect::<Vec<_>>();
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        let mut invalid_loader_cpi = WithdrawalCpi {
            fail: false,
            calls: 0,
        };
        assert_eq!(
            process_pair_forest_terminal_with_verifier_v1(
                &program_id,
                &infos,
                &instruction,
                1,
                &Rent::default(),
                &mut invalid_loader_cpi,
                |_, _, _, _, _, _, _, _, _, _, _| panic!("invalid loader reached verifier"),
                |_| {},
            ),
            Err(PoolV1ProgramError::InvalidTokenProgram.into()),
        );
        drop(infos);
        assert_eq!(invalid_loader_cpi.calls, 0);
        assert_eq!(
            accounts
                .iter()
                .map(|account| account.data.clone())
                .collect::<Vec<_>>(),
            invalid_loader_before,
        );
        accounts[token_program_index].owner = bpf_loader::id();

        // B4-style Pool-only vault hints: every wrong authority or vault
        // token bump rejects with the existing custody address errors before
        // the verifier or any CPI.
        let hint_start = instruction.len() - POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES;
        let mut vault_rejections = 0;
        for (offset, expected) in [
            (2usize, PoolV1ProgramError::InvalidVaultAuthority),
            (3, PoolV1ProgramError::InvalidVaultTokenAddress),
        ] {
            let canonical = instruction[hint_start + offset];
            assert_ne!(canonical, 0);
            for bump in 0..=255u8 {
                if bump == canonical {
                    continue;
                }
                let mut data = instruction.clone();
                data[hint_start + offset] = bump;
                assert_eq!(
                    reject_before_cpi(&program_id, &mut accounts, &data),
                    Err(expected.into()),
                    "vault hint {offset} bump {bump}"
                );
                vault_rejections += 1;
            }
        }
        assert_eq!(vault_rejections, 510);

        let before = accounts
            .iter()
            .map(|account| account.data.clone())
            .collect::<Vec<_>>();
        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        let mut failing = WithdrawalCpi {
            fail: true,
            calls: 0,
        };
        assert!(process_pair_forest_terminal_with_verifier_v1(
            &program_id,
            &infos,
            &instruction,
            1,
            &Rent::default(),
            &mut failing,
            |_, _, _, _, _, _, _, _, _, _, _| Ok(AuthenticatedPairForestResultV1::for_test(result)),
            |_| {},
        )
        .is_err());
        drop(infos);
        assert_eq!(failing.calls, 1);
        assert_eq!(
            accounts.iter().map(|a| a.data.clone()).collect::<Vec<_>>(),
            before
        );

        let infos: Vec<_> = accounts.iter_mut().map(TestAccount::info).collect();
        let mut success = WithdrawalCpi {
            fail: false,
            calls: 0,
        };
        process_pair_forest_terminal_with_verifier_v1(
            &program_id,
            &infos,
            &instruction,
            1,
            &Rent::default(),
            &mut success,
            |_, _, _, _, _, _, _, _, _, _, _| Ok(AuthenticatedPairForestResultV1::for_test(result)),
            |_| {},
        )
        .unwrap();
        drop(infos);
        assert_eq!(success.calls, 1);
        assert_eq!(
            u64::from_le_bytes(accounts[12].data[64..72].try_into().unwrap()),
            75
        );
        assert_eq!(
            u64::from_le_bytes(accounts[13].data[64..72].try_into().unwrap()),
            35
        );
        assert!(accounts[4].data.iter().any(|byte| *byte != 0));
    }
}

#[cfg(kani)]
mod Hir_checkpoint_guards {
    use super::*;

    #[kani::proof]
    #[kani::unwind(195)]
    fn Hir_occupied_guard_rejects() {
        let id = Pubkey::new_from_array([7; 32]);
        let address = Pubkey::new_from_array([8; 32]);
        let mut bytes: [u8; 192] = kani::any();
        kani::assume(bytes[0] != 0);
        let original = bytes;
        let mut lamports = u64::MAX;
        let account = AccountInfo::new(&address, false, true, &mut lamports,
            &mut bytes, &id, false, 0);
        let result = require_program_owned_zeroed(&account, &id, 192, &Rent::default());
        assert!(result.is_err());
        drop(account);
        assert!(bytes == original);
    }

    #[kani::proof]
    #[kani::unwind(195)]
    fn Hir_occupied_plan_rejects() {
        let id = Pubkey::new_from_array([7; 32]);
        let address = Pubkey::new_from_array([8; 32]);
        let mut bytes: [u8; 192] = kani::any();
        kani::assume(bytes[0] != 0);
        let original = bytes;
        let mut lamports = u64::MAX;
        let account = AccountInfo::new(&address, false, true, &mut lamports,
            &mut bytes, &id, false, 0);
        let result = crate::processor::plan_fresh_program_pda(&account, &id, &address, 192);
        assert!(result.is_err());
        drop(account);
        assert!(bytes == original);
    }
}
