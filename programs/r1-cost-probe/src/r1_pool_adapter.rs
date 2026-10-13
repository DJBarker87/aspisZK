//! Default-off local lifecycle and Pool adapter for measuring the R1 S2 split.
//!
//! ASQ8 authentication and reconstruction are copied from the verifier's
//! `v7_pair_forest_dispatch` path. This module keeps the audit-pinned Pool,
//! registry, and policy bindings while replacing only its proof engine with
//! the R1 `tx1`/`tx2` checkpoints. Lifecycle support is a local prototype,
//! not a production account-lifecycle release.

extern crate alloc;

use alloc::boxed::Box;
use aspis_core::field::M31;
use aspis_r1_cost_probe::{transport::Variant, verifier};
use aspis_statement::decode_digest_canonical;
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_forest_checkpoint_v1, decode_pool_v1_pair_forest_master_v1,
    decode_pool_v1_pair_forest_terminal_request_v1,
    decode_pool_v1_pair_forest_terminal_statement_v1, decode_pool_v1_pair_verified_afterstate_v1,
    decode_verifier_registry_entry_v1, decode_verifier_registry_entry_v2,
    decode_verifier_registry_v1, decode_verifier_registry_v2,
    encode_pool_v1_pair_forest_terminal_result_v1,
    encode_pool_v1_pair_forest_terminal_statement_v1, encode_pool_v1_pair_verified_afterstate_v1,
    pool_v1_pair_forest_output_lane_v1,
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1,
    validate_pool_v1_pair_forest_terminal_statement_v1, validate_verifier_policy_v1,
    IncrementalMerkleTreeV1, PoolV1PairForestCheckpointV1, PoolV1PairForestLaneStateV1,
    PoolV1PairForestMasterV1, PoolV1PairForestTerminalCommonV1, PoolV1PairForestTerminalPaymentV1,
    PoolV1PairForestTerminalRequestV1, PoolV1PairForestTerminalResultV1,
    PoolV1PairForestTerminalStatementV1, PoolV1PairLatePublicStatementV1, PoolV1PairLiveSnapshotV1,
    POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_PAIR_CAPACITY,
    POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING, POOL_V1_PAIR_FOREST_ALL_LANES_MASK,
    POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_COUNT,
    POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES, POOL_V1_PAIR_FOREST_LANE_MAGIC,
    POOL_V1_PAIR_FOREST_LANE_VERSION, POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES,
    POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC, POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES,
    POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC, POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES,
    POOL_V1_PAIR_FOREST_TERMINAL_VERSION, POOL_V1_PAIR_TREE_DEPTH,
    POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, POOL_V1_TREE_HASH_VERSION, POOL_V1_TREE_STATE_MAGIC,
    POOL_V1_TREE_STATE_VERSION, POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT,
    POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY, POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES,
    POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
};
use solana_program::{
    account_info::AccountInfo, bpf_loader_upgradeable, clock::Clock, entrypoint::ProgramResult,
    hash::hashv, msg, program, program_error::ProgramError, pubkey::Pubkey, sysvar::Sysvar,
};

#[path = "../../aspis-verifier/src/v7_pair_empty_roots.rs"]
mod v7_pair_empty_roots;

const ASPU_HEADER: usize = POOL_V1_VERIFIER_PROOF_ACCOUNT_HEADER_BYTES;
const ASPU_AUTHORITY: core::ops::Range<usize> = 8..40;
const CHECKPOINT_TAIL_BYTES: usize = 1_768;
const ASRU_MAGIC: [u8; 4] = *b"ASRU";
const ASRU_BODY_BYTES: usize = POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES;
const PROFILE_BINDING: [u8; 32] = [
    0x78, 0x17, 0x1b, 0x56, 0x9e, 0xa7, 0xbc, 0xe5, 0x97, 0x63, 0xa2, 0xb5, 0x78, 0x81, 0x06, 0xa7,
    0x49, 0xbe, 0xd7, 0x47, 0x75, 0x6c, 0xf2, 0xd2, 0x00, 0x69, 0x99, 0x37, 0x92, 0x19, 0x13, 0xe9,
];
const RELEASE_BINDING: [u8; 32] = [
    0x45, 0x90, 0xcd, 0x06, 0x35, 0x37, 0xb3, 0xb0, 0x2f, 0xae, 0xb1, 0x0d, 0x9a, 0x7f, 0x39, 0x99,
    0x3f, 0xbe, 0x4b, 0xb6, 0x20, 0x30, 0x53, 0x32, 0x8d, 0x60, 0x0d, 0xbd, 0x48, 0x1c, 0xe0, 0x34,
];
const AUDIT_POOL_PROGRAM: [u8; 32] = [0x41; 32];
const AUDIT_REGISTRY_PROGRAM: [u8; 32] = [0x44; 32];
const AUDIT_POLICY_BINDING: [u8; 32] = [7; 32];

const PAIR_FOREST_MASTER_SEED: &[u8] = b"aspis-pair-forest-master-v1";
const PAIR_FOREST_LANE_SEED: &[u8] = b"aspis-pair-forest-lane-v1";
const PAIR_FOREST_CHECKPOINT_SEED: &[u8] = b"aspis-pair-forest-checkpoint-v1";
const VERIFIER_REGISTRY_SEED: &[u8] = b"aspis-verifier-registry-v1";
const VERIFIER_ENTRY_SEED: &[u8] = b"aspis-verifier-entry-v1";
const VERIFIER_REGISTRY_V2_SEED: &[u8] = b"aspis-verifier-registry-v2";
const VERIFIER_ENTRY_V2_SEED: &[u8] = b"aspis-verifier-entry-v2";
const _: () = assert!(ASPU_HEADER == 40);

#[derive(Clone, Copy, PartialEq, Eq)]
enum LifecycleKind {
    Proof,
    Public,
}

impl LifecycleKind {
    fn from_byte(value: u8) -> Result<Self, ProgramError> {
        match value {
            0 => Ok(Self::Proof),
            1 => Ok(Self::Public),
            _ => Err(ProgramError::InvalidInstructionData),
        }
    }

    fn magic(self) -> [u8; 4] {
        match self {
            Self::Proof => POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC,
            Self::Public => ASRU_MAGIC,
        }
    }

    fn body_len(self) -> Result<usize, ProgramError> {
        match self {
            Self::Proof => POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
                .checked_add(verifier::View::proof_bytes(Variant::S2))
                .and_then(|length| length.checked_add(CHECKPOINT_TAIL_BYTES))
                .ok_or(ProgramError::InvalidAccountData),
            Self::Public => Ok(ASRU_BODY_BYTES),
        }
    }

    fn writable_prefix_len(self) -> Result<usize, ProgramError> {
        match self {
            Self::Proof => POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
                .checked_add(verifier::View::proof_bytes(Variant::S2))
                .ok_or(ProgramError::InvalidAccountData),
            Self::Public => Ok(ASRU_BODY_BYTES),
        }
    }
}

struct AuthenticatedAsq8Accounts {
    master_account: [u8; 32],
    checkpoint_account: [u8; 32],
    selected_lane_account: [u8; 32],
    master: Box<PoolV1PairForestMasterV1>,
    checkpoint: Box<PoolV1PairForestCheckpointV1>,
    selected_lane: Box<PoolV1PairForestLaneStateV1>,
    live_snapshot: Box<PoolV1PairLiveSnapshotV1>,
}

struct ScannedAsqaProof {
    candidate_afterstate: Box<aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1>,
    proof_length: usize,
}

struct ValidatedAsqa {
    statement: Box<PoolV1PairForestTerminalStatementV1>,
    proof_length: usize,
}

fn require_readonly_account(account: &AccountInfo<'_>, owner: &Pubkey) -> ProgramResult {
    if account.owner != owner || account.is_signer || account.is_writable || account.executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

fn require_distinct_accounts<const N: usize>(accounts: &[&AccountInfo<'_>; N]) -> ProgramResult {
    for (index, account) in accounts.iter().enumerate() {
        if accounts[..index]
            .iter()
            .any(|previous| previous.key == account.key)
        {
            return Err(ProgramError::InvalidArgument);
        }
    }
    Ok(())
}

#[inline(never)]
fn decode_public_statement_box(
    bytes: &[u8],
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_forest_terminal_statement_v1(bytes)
            .map_err(|_| ProgramError::InvalidAccountData)?,
    ))
}

#[inline(never)]
fn lifecycle_accounts<'a, 'info>(
    program_id: &Pubkey,
    accounts: &'a [AccountInfo<'info>],
) -> Result<(&'a AccountInfo<'info>, &'a AccountInfo<'info>), ProgramError> {
    let [target, authority] = accounts else {
        return Err(if accounts.len() < 2 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    if target.key == authority.key
        || target.owner != program_id
        || !target.is_writable
        || target.is_signer
        || target.executable
        || authority.is_writable
        || !authority.is_signer
        || authority.executable
        || authority.key.to_bytes() == [0; 32]
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok((target, authority))
}

#[inline(never)]
fn validate_lifecycle_header(
    data: &[u8],
    authority: &Pubkey,
    sealed: bool,
) -> Result<LifecycleKind, ProgramError> {
    if data.len() < ASPU_HEADER {
        return Err(ProgramError::InvalidAccountData);
    }
    let kind = if data[..4] == POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC {
        LifecycleKind::Proof
    } else if data[..4] == ASRU_MAGIC {
        LifecycleKind::Public
    } else {
        return Err(ProgramError::InvalidAccountData);
    };
    let body_len = kind.body_len()?;
    let encoded_body_len = u32::from_le_bytes(
        data[4..8]
            .try_into()
            .map_err(|_| ProgramError::InvalidAccountData)?,
    ) as usize;
    let auth = &data[ASPU_AUTHORITY.clone()];
    let authority_bytes = authority.to_bytes();
    let auth_valid = if sealed {
        auth.iter().all(|byte| *byte == 0)
    } else {
        auth == authority_bytes.as_slice() && auth.iter().any(|byte| *byte != 0)
    };
    if encoded_body_len != body_len || data.len() != ASPU_HEADER + body_len || !auth_valid {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(kind)
}

#[inline(never)]
fn validate_lifecycle_final_body(data: &[u8], kind: LifecycleKind) -> ProgramResult {
    match kind {
        LifecycleKind::Proof => {
            let candidate_end = ASPU_HEADER + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
            let proof_end = candidate_end + verifier::View::proof_bytes(Variant::S2);
            let candidate_bytes = &data[ASPU_HEADER..candidate_end];
            let candidate = decode_pool_v1_pair_verified_afterstate_v1(candidate_bytes)
                .map_err(|_| ProgramError::InvalidAccountData)?;
            if encode_pool_v1_pair_verified_afterstate_v1(&candidate)
                .map_err(|_| ProgramError::InvalidAccountData)?
                .as_ref()
                != candidate_bytes
            {
                return Err(ProgramError::InvalidAccountData);
            }
            let proof = verifier::View::parse(&data[candidate_end..proof_end])
                .map_err(|_| ProgramError::InvalidAccountData)?;
            if proof.variant != Variant::S2
                || data[proof_end..].len() != CHECKPOINT_TAIL_BYTES
                || data[proof_end..].iter().any(|byte| *byte != 0)
            {
                return Err(ProgramError::InvalidAccountData);
            }
        }
        LifecycleKind::Public => {
            let statement = decode_public_statement_box(&data[ASPU_HEADER..])?;
            validate_pool_v1_pair_forest_terminal_statement_v1(&statement)
                .map_err(|_| ProgramError::InvalidAccountData)?;
        }
    }
    Ok(())
}

#[inline(never)]
fn lifecycle_init(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    if instruction_data.len() != 2 || instruction_data[0] != 4 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let kind = LifecycleKind::from_byte(instruction_data[1])?;
    let (target, authority) = lifecycle_accounts(program_id, accounts)?;
    let body_len = kind.body_len()?;
    if u32::try_from(body_len).is_err() {
        return Err(ProgramError::InvalidInstructionData);
    }
    let mut target_data = target.try_borrow_mut_data()?;
    if target_data.len() != ASPU_HEADER + body_len || target_data.iter().any(|byte| *byte != 0) {
        return Err(ProgramError::AccountAlreadyInitialized);
    }
    target_data[..4].copy_from_slice(&kind.magic());
    target_data[4..8].copy_from_slice(&(body_len as u32).to_le_bytes());
    target_data[ASPU_AUTHORITY.clone()].copy_from_slice(authority.key.as_ref());
    Ok(())
}

#[inline(never)]
fn lifecycle_write(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    if instruction_data.len() <= 5 || instruction_data[0] != 5 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let (target, authority) = lifecycle_accounts(program_id, accounts)?;
    let offset = u32::from_le_bytes(
        instruction_data[1..5]
            .try_into()
            .map_err(|_| ProgramError::InvalidInstructionData)?,
    ) as usize;
    let payload = &instruction_data[5..];
    let kind = {
        let target_data = target.try_borrow_data()?;
        validate_lifecycle_header(&target_data, authority.key, false)?
    };
    let end = offset
        .checked_add(payload.len())
        .ok_or(ProgramError::InvalidInstructionData)?;
    if end > kind.writable_prefix_len()? || end > kind.body_len()? {
        return Err(ProgramError::InvalidInstructionData);
    }
    let mut target_data = target.try_borrow_mut_data()?;
    let start = ASPU_HEADER
        .checked_add(offset)
        .ok_or(ProgramError::InvalidInstructionData)?;
    let write_end = start
        .checked_add(payload.len())
        .ok_or(ProgramError::InvalidInstructionData)?;
    target_data[start..write_end].copy_from_slice(payload);
    Ok(())
}

#[inline(never)]
fn lifecycle_finalize(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> ProgramResult {
    if instruction_data != &[6] {
        return Err(ProgramError::InvalidInstructionData);
    }
    let (target, authority) = lifecycle_accounts(program_id, accounts)?;
    let kind = {
        let target_data = target.try_borrow_data()?;
        let kind = validate_lifecycle_header(&target_data, authority.key, false)?;
        validate_lifecycle_final_body(&target_data, kind)?;
        kind
    };
    let mut target_data = target.try_borrow_mut_data()?;
    if target_data[..4] != kind.magic() {
        return Err(ProgramError::InvalidAccountData);
    }
    target_data[ASPU_AUTHORITY.clone()].fill(0);
    Ok(())
}

#[inline(never)]
fn decode_master_box(bytes: &[u8]) -> Result<Box<PoolV1PairForestMasterV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_forest_master_v1(bytes)
            .map_err(|_| ProgramError::InvalidAccountData)?,
    ))
}

#[inline(never)]
fn decode_checkpoint_box(bytes: &[u8]) -> Result<Box<PoolV1PairForestCheckpointV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_forest_checkpoint_v1(bytes)
            .map_err(|_| ProgramError::InvalidAccountData)?,
    ))
}

/// Exact source-release lane decoder copied from the ASQ8 audit path. It
/// retains the pinned account format, frontier canonicality, and empty-root
/// conditions for each unoccupied subtree.
#[inline(never)]
fn decode_lane_from_pool_release(
    bytes: &[u8],
) -> Result<Box<PoolV1PairForestLaneStateV1>, ProgramError> {
    use v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS;
    if bytes.len() != POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES
        || bytes[..4] != POOL_V1_PAIR_FOREST_LANE_MAGIC
        || bytes[4] != POOL_V1_PAIR_FOREST_LANE_VERSION
        || usize::from(bytes[5]) >= POOL_V1_PAIR_FOREST_LANE_COUNT
        || bytes[6] != POOL_V1_PAIR_FOREST_LANE_COUNT as u8
        || bytes[7] != POOL_V1_PAIR_TREE_DEPTH as u8
        || bytes[8..40] != POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING
        || bytes[72..POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES]
            .iter()
            .any(|byte| *byte != 0)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let master: [u8; 32] = bytes[40..72]
        .try_into()
        .map_err(|_| ProgramError::InvalidAccountData)?;
    if master == [0u8; 32] {
        return Err(ProgramError::InvalidAccountData);
    }
    let tree = &bytes[POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES..];
    if tree[..4] != POOL_V1_TREE_STATE_MAGIC
        || tree[4] != POOL_V1_TREE_STATE_VERSION
        || tree[5] != POOL_V1_PAIR_TREE_DEPTH as u8
        || tree[6] != POOL_V1_TREE_HASH_VERSION
        || tree[7] != POOL_V1_DIGEST_ENCODING_VERSION
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let next_leaf_index = u64::from_le_bytes(
        tree[8..16]
            .try_into()
            .map_err(|_| ProgramError::InvalidAccountData)?,
    );
    if next_leaf_index > POOL_V1_PAIR_CAPACITY {
        return Err(ProgramError::InvalidAccountData);
    }
    let root = decode_digest_canonical(
        tree[16..48]
            .try_into()
            .map_err(|_| ProgramError::InvalidAccountData)?,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    let mut frontier = [[M31::ZERO; 8]; POOL_V1_PAIR_TREE_DEPTH];
    for (level, node) in frontier.iter_mut().enumerate() {
        let start = 48 + 32 * level;
        *node = decode_digest_canonical(
            tree[start..start + 32]
                .try_into()
                .map_err(|_| ProgramError::InvalidAccountData)?,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if (next_leaf_index >> level) & 1 == 0 && *node != V7_PAIR_EMPTY_ROOTS[level] {
            return Err(ProgramError::InvalidAccountData);
        }
    }
    if next_leaf_index == 0 && root != V7_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH] {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(Box::new(PoolV1PairForestLaneStateV1 {
        master,
        lane_id: bytes[5],
        tree: IncrementalMerkleTreeV1 {
            next_leaf_index,
            root,
            frontier,
        },
    }))
}

#[inline(never)]
fn authenticate_invariant_release_registry(
    verifier_program: &Pubkey,
    pool_program: &Pubkey,
    master_account: &AccountInfo<'_>,
    master: &PoolV1PairForestMasterV1,
    registry_account: &AccountInfo<'_>,
    entry_account: &AccountInfo<'_>,
    current_slot: u64,
) -> ProgramResult {
    if pool_program.to_bytes() != AUDIT_POOL_PROGRAM
        || master.verifier_policy.flags & POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY == 0
        || master.verifier_policy.registry_program != AUDIT_REGISTRY_PROGRAM
        || master.verifier_policy.registry_authority != [0u8; 32]
        || master.verifier_policy.policy_binding != AUDIT_POLICY_BINDING
    {
        return Err(ProgramError::InvalidAccountData);
    }
    validate_verifier_policy_v1(&master.verifier_policy)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let registry_program = Pubkey::new_from_array(AUDIT_REGISTRY_PROGRAM);
    require_readonly_account(registry_account, &registry_program)?;
    let immutable_deployment =
        master.verifier_policy.flags & POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0;
    if immutable_deployment {
        let loader = bpf_loader_upgradeable::id();
        let expected_registry = Pubkey::find_program_address(
            &[VERIFIER_REGISTRY_V2_SEED, master_account.key.as_ref()],
            &registry_program,
        )
        .0;
        if registry_account.key != &expected_registry {
            return Err(ProgramError::InvalidAccountData);
        }
        let registry = decode_verifier_registry_v2(&registry_account.try_borrow_data()?)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        let registry_programdata =
            Pubkey::find_program_address(&[registry_program.as_ref()], &loader).0;
        if registry.pool != master_account.key.to_bytes()
            || registry.authority != master.verifier_policy.registry_authority
            || registry.policy_binding != master.verifier_policy.policy_binding
            || registry.registry_program != registry_program.to_bytes()
            || registry.loader_program != loader.to_bytes()
            || registry.programdata_address != registry_programdata.to_bytes()
            || !registry.is_immutable()
            || registry.is_paused()
        {
            return Err(ProgramError::InvalidAccountData);
        }
        require_readonly_account(entry_account, &registry_program)?;
        let expected_entry = Pubkey::find_program_address(
            &[
                VERIFIER_ENTRY_V2_SEED,
                master_account.key.as_ref(),
                &PROFILE_BINDING,
                &RELEASE_BINDING,
            ],
            &registry_program,
        )
        .0;
        if entry_account.key != &expected_entry {
            return Err(ProgramError::InvalidAccountData);
        }
        let entry = decode_verifier_registry_entry_v2(&entry_account.try_borrow_data()?)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        let verifier_programdata =
            Pubkey::find_program_address(&[verifier_program.as_ref()], &loader).0;
        if entry.pool != master_account.key.to_bytes()
            || entry.policy_binding != AUDIT_POLICY_BINDING
            || entry.verifier_program != verifier_program.to_bytes()
            || entry.profile_binding != PROFILE_BINDING
            || entry.release_binding != RELEASE_BINDING
            || entry.statement_version != POOL_V1_PAIR_FOREST_TERMINAL_VERSION
            || entry.loader_program != loader.to_bytes()
            || entry.programdata_address != verifier_programdata.to_bytes()
            || entry.expected_upgrade_authority != [0u8; 32]
            || !entry.is_active_at(current_slot)
        {
            return Err(ProgramError::InvalidAccountData);
        }
        return Ok(());
    }

    let expected_registry = Pubkey::find_program_address(
        &[VERIFIER_REGISTRY_SEED, master_account.key.as_ref()],
        &registry_program,
    )
    .0;
    if registry_account.key != &expected_registry {
        return Err(ProgramError::InvalidAccountData);
    }
    let registry = decode_verifier_registry_v1(&registry_account.try_borrow_data()?)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    if registry.pool != master_account.key.to_bytes()
        || registry.authority != master.verifier_policy.registry_authority
        || registry.policy_binding != master.verifier_policy.policy_binding
        || !registry.is_immutable()
        || registry.is_paused()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    require_readonly_account(entry_account, &registry_program)?;
    let expected_entry = Pubkey::find_program_address(
        &[
            VERIFIER_ENTRY_SEED,
            master_account.key.as_ref(),
            &PROFILE_BINDING,
            &RELEASE_BINDING,
        ],
        &registry_program,
    )
    .0;
    if entry_account.key != &expected_entry {
        return Err(ProgramError::InvalidAccountData);
    }
    let entry = decode_verifier_registry_entry_v1(&entry_account.try_borrow_data()?)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    if entry.pool != master_account.key.to_bytes()
        || entry.policy_binding != AUDIT_POLICY_BINDING
        || entry.verifier_program != verifier_program.to_bytes()
        || entry.profile_binding != PROFILE_BINDING
        || entry.release_binding != RELEASE_BINDING
        || entry.statement_version != POOL_V1_PAIR_FOREST_TERMINAL_VERSION
        || !entry.is_active_at(current_slot)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

#[inline(never)]
fn authenticate_asq8_accounts(
    verifier_program: &Pubkey,
    accounts: &[AccountInfo<'_>],
    pool_program: &Pubkey,
    output_lane: u8,
    current_slot: u64,
) -> Result<AuthenticatedAsq8Accounts, ProgramError> {
    let [proof_account, master_account, checkpoint_account, lane_account, registry_account, entry_account] =
        accounts
    else {
        return Err(if accounts.len() < 6 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    require_readonly_account(proof_account, verifier_program)?;
    require_readonly_account(master_account, pool_program)?;
    require_readonly_account(checkpoint_account, pool_program)?;
    require_readonly_account(lane_account, pool_program)?;
    require_distinct_accounts(&[
        proof_account,
        master_account,
        checkpoint_account,
        lane_account,
        registry_account,
        entry_account,
    ])?;

    let master = decode_master_box(&master_account.try_borrow_data()?)?;
    if master.identity.pool != master_account.key.to_bytes()
        || master.initialized_lane_mask != POOL_V1_PAIR_FOREST_ALL_LANES_MASK
        || Pubkey::find_program_address(
            &[
                PAIR_FOREST_MASTER_SEED,
                Pubkey::new_from_array(master.identity.asset_mint).as_ref(),
            ],
            pool_program,
        )
        .0 != *master_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }
    authenticate_invariant_release_registry(
        verifier_program,
        pool_program,
        master_account,
        &master,
        registry_account,
        entry_account,
        current_slot,
    )?;

    let checkpoint = decode_checkpoint_box(&checkpoint_account.try_borrow_data()?)?;
    if checkpoint.master != master_account.key.to_bytes()
        || checkpoint.deployment_domain != master.identity.deployment_domain
        || Pubkey::find_program_address(
            &[
                PAIR_FOREST_CHECKPOINT_SEED,
                master_account.key.as_ref(),
                &checkpoint.checkpoint_sequence.to_le_bytes(),
            ],
            pool_program,
        )
        .0 != *checkpoint_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let selected_lane = decode_lane_from_pool_release(&lane_account.try_borrow_data()?)?;
    if selected_lane.master != master_account.key.to_bytes()
        || selected_lane.lane_id != output_lane
        || Pubkey::find_program_address(
            &[
                PAIR_FOREST_LANE_SEED,
                master_account.key.as_ref(),
                &[output_lane],
            ],
            pool_program,
        )
        .0 != *lane_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let live_snapshot = Box::new(PoolV1PairLiveSnapshotV1 {
        pool: master_account.key.to_bytes(),
        deployment_domain: master.identity.deployment_domain,
        sequence: selected_lane.tree.next_leaf_index,
        next_pair_index: selected_lane.tree.next_leaf_index,
        current_root: selected_lane.tree.root,
        frontier: selected_lane.tree.frontier,
    });
    Ok(AuthenticatedAsq8Accounts {
        master_account: master_account.key.to_bytes(),
        checkpoint_account: checkpoint_account.key.to_bytes(),
        selected_lane_account: lane_account.key.to_bytes(),
        master,
        checkpoint,
        selected_lane,
        live_snapshot,
    })
}

#[inline(never)]
fn scan_aspu_body(bytes: &[u8]) -> Result<ScannedAsqaProof, ProgramError> {
    let proof_length = verifier::View::proof_bytes(Variant::S2);
    let expected_body = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
        .checked_add(proof_length)
        .and_then(|length| length.checked_add(CHECKPOINT_TAIL_BYTES))
        .ok_or(ProgramError::InvalidAccountData)?;
    if bytes.len() != ASPU_HEADER + expected_body
        || bytes.len() < ASPU_HEADER
        || bytes[..4] != POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC
        || bytes[ASPU_AUTHORITY.clone()].iter().any(|byte| *byte != 0)
        || u32::from_le_bytes(
            bytes[4..8]
                .try_into()
                .map_err(|_| ProgramError::InvalidAccountData)?,
        ) as usize
            != expected_body
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let candidate_start = ASPU_HEADER;
    let proof_start = candidate_start + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let proof_end = proof_start + proof_length;
    let candidate_bytes = &bytes[candidate_start..proof_start];
    let candidate = Box::new(
        decode_pool_v1_pair_verified_afterstate_v1(candidate_bytes)
            .map_err(|_| ProgramError::InvalidAccountData)?,
    );
    if encode_pool_v1_pair_verified_afterstate_v1(&candidate)
        .map_err(|_| ProgramError::InvalidAccountData)?
        .as_ref()
        != candidate_bytes
        || bytes[proof_start + 8] != Variant::S2.tag()
        || bytes[proof_end..].len() != CHECKPOINT_TAIL_BYTES
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(ScannedAsqaProof {
        candidate_afterstate: candidate,
        proof_length,
    })
}

#[inline(never)]
fn asq8_common(
    authenticated: &AuthenticatedAsq8Accounts,
    candidate_afterstate: &aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1,
) -> Box<PoolV1PairForestTerminalCommonV1> {
    Box::new(PoolV1PairForestTerminalCommonV1 {
        master_account: authenticated.master_account,
        checkpoint_account: authenticated.checkpoint_account,
        selected_lane_account: authenticated.selected_lane_account,
        output_lane: authenticated.selected_lane.lane_id,
        checkpoint_sequence: authenticated.checkpoint.checkpoint_sequence,
        historical_global_anchor: authenticated.checkpoint.global_root,
        lane_transition: PoolV1PairLatePublicStatementV1 {
            live_snapshot: *authenticated.live_snapshot,
            candidate_afterstate: *candidate_afterstate,
        },
    })
}

#[inline(never)]
fn transfer_statement_box(
    common: Box<PoolV1PairForestTerminalCommonV1>,
    public: aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1,
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    let statement = Box::new(PoolV1PairForestTerminalStatementV1::PrivateTransfer {
        common: *common,
        public,
    });
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok(statement)
}

#[inline(never)]
fn withdrawal_statement_box(
    common: Box<PoolV1PairForestTerminalCommonV1>,
    public: aspis_statement::pool_v1::PoolV1WithdrawalPublicV1,
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    let statement = Box::new(PoolV1PairForestTerminalStatementV1::Withdrawal {
        common: *common,
        public,
    });
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    Ok(statement)
}

#[inline(never)]
fn reconstruct_asq8_statement(
    request: &PoolV1PairForestTerminalRequestV1,
    authenticated: &AuthenticatedAsq8Accounts,
    candidate_afterstate: &aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1,
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    if authenticated.live_snapshot.next_pair_index.checked_add(1)
        != Some(candidate_afterstate.next_pair_index)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let requested_asset_id = match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => public.asset_id,
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => public.asset_id,
    };
    if authenticated.master.identity.asset_id != requested_asset_id {
        return Err(ProgramError::InvalidInstructionData);
    }
    let common = asq8_common(authenticated, candidate_afterstate);
    match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public) => {
            transfer_statement_box(common, public)
        }
        PoolV1PairForestTerminalPaymentV1::Withdrawal(public) => {
            withdrawal_statement_box(common, public)
        }
    }
}

#[inline(never)]
fn validate_asq8(
    verifier_program: &Pubkey,
    accounts: &[AccountInfo<'_>],
    instruction_data: &[u8],
) -> Result<ValidatedAsqa, ProgramError> {
    if instruction_data.len() != POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES {
        return Err(ProgramError::InvalidInstructionData);
    }
    let request = decode_pool_v1_pair_forest_terminal_request_v1(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if request.verifier_profile != PROFILE_BINDING
        || request.verifier_release != RELEASE_BINDING
        || request.pool_program != AUDIT_POOL_PROGRAM
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    let pool_program = Pubkey::new_from_array(request.pool_program);
    let output_lane = pool_v1_pair_forest_output_lane_v1(request.public.nullifier())
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let authenticated = authenticate_asq8_accounts(
        verifier_program,
        accounts,
        &pool_program,
        output_lane,
        Clock::get()?.slot,
    )?;
    let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let scanned = scan_aspu_body(&proof_account.try_borrow_data()?)?;
    let statement =
        reconstruct_asq8_statement(&request, &authenticated, &scanned.candidate_afterstate)?;
    Ok(ValidatedAsqa {
        statement,
        proof_length: scanned.proof_length,
    })
}

#[inline(never)]
fn emit_result(statement: &PoolV1PairForestTerminalStatementV1) -> ProgramResult {
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: statement.transition_kind(),
        master_account: statement.common().master_account,
        selected_lane_account: statement.common().selected_lane_account,
        output_lane: statement.common().output_lane,
        nullifier: *statement.nullifier(),
        verified_afterstate: statement.common().lane_transition.candidate_afterstate,
    };
    validate_pool_v1_pair_forest_terminal_result_against_statement_v1(statement, &result)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let encoded = encode_pool_v1_pair_forest_terminal_result_v1(&result)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if encoded.len() != POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES
        || encoded[..4] != POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    program::set_return_data(&encoded);
    Ok(())
}

#[inline(never)]
fn stage1(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult {
    if data != &[3, 10] || accounts.len() != 2 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let proof_account = &accounts[0];
    let public_account = &accounts[1];
    if proof_account.key == public_account.key
        || proof_account.owner != program_id
        || !proof_account.is_writable
        || proof_account.executable
        || proof_account.is_signer
        || public_account.owner != program_id
        || public_account.is_writable
        || public_account.executable
        || public_account.is_signer
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let public_data = public_account.try_borrow_data()?;
    if validate_lifecycle_header(&public_data, &Pubkey::default(), true)? != LifecycleKind::Public {
        return Err(ProgramError::InvalidAccountData);
    }
    let public_bytes = &public_data[ASPU_HEADER..];
    let statement = decode_public_statement_box(public_bytes)?;
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let candidate = encode_pool_v1_pair_verified_afterstate_v1(
        &statement.common().lane_transition.candidate_afterstate,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;

    let mut proof_data = proof_account.try_borrow_mut_data()?;
    let proof_length = verifier::View::proof_bytes(Variant::S2);
    let body_length = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
        .checked_add(proof_length)
        .and_then(|length| length.checked_add(CHECKPOINT_TAIL_BYTES))
        .ok_or(ProgramError::InvalidAccountData)?;
    if verifier::checkpoint_size(Variant::S2) != CHECKPOINT_TAIL_BYTES
        || proof_data.len() != ASPU_HEADER + body_length
        || proof_data[..4] != POOL_V1_VERIFIER_PROOF_ACCOUNT_MAGIC
        || proof_data[ASPU_AUTHORITY.clone()]
            .iter()
            .any(|byte| *byte != 0)
        || u32::from_le_bytes(
            proof_data[4..8]
                .try_into()
                .map_err(|_| ProgramError::InvalidAccountData)?,
        ) as usize
            != body_length
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let candidate_start = ASPU_HEADER;
    let proof_start = candidate_start + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let proof_end = proof_start + proof_length;
    if proof_data[candidate_start..proof_start] != candidate
        || proof_data[proof_start + 8] != Variant::S2.tag()
        || proof_data[proof_end..].iter().any(|byte| *byte != 0)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let checkpoint = super::first(public_bytes, &proof_data[proof_start..proof_end], 10)?;
    if checkpoint.len() != CHECKPOINT_TAIL_BYTES {
        return Err(ProgramError::InvalidAccountData);
    }
    proof_data[proof_end..].copy_from_slice(&checkpoint);
    msg!("r1:pool-adapter-stage1-checkpoint-written");
    solana_program::log::sol_log_compute_units();
    Ok(())
}

#[inline(never)]
fn stage2(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult {
    if accounts.len() != 6 || data.get(..4) != Some(&POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[..])
    {
        return Err(ProgramError::InvalidInstructionData);
    }
    program::set_return_data(&[]);
    msg!("r1:pool-adapter-stage2-begin");
    solana_program::log::sol_log_compute_units();
    let validated = validate_asq8(program_id, accounts, data)?;
    let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let proof_data = proof_account.try_borrow_data()?;
    let proof_length = validated.proof_length;
    let proof_start = ASPU_HEADER + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let proof_end = proof_start + proof_length;
    let checkpoint_end = proof_end + CHECKPOINT_TAIL_BYTES;
    if proof_data.len() != checkpoint_end
        || u32::from_le_bytes(
            proof_data[4..8]
                .try_into()
                .map_err(|_| ProgramError::InvalidAccountData)?,
        ) as usize
            != proof_data.len() - ASPU_HEADER
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let public_bytes = encode_pool_v1_pair_forest_terminal_statement_v1(&validated.statement)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    if public_bytes.len() != POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES {
        return Err(ProgramError::InvalidInstructionData);
    }
    verifier::tx2_authenticated(
        &public_bytes,
        &proof_data[proof_start..proof_end],
        &proof_data[proof_end..checkpoint_end],
        |parts| hashv(parts).to_bytes(),
        Some(super::mark),
    )
    .map_err(super::error)?;
    emit_result(&validated.statement)
}

#[inline(never)]
pub(super) fn process(
    program_id: &Pubkey,
    accounts: &[AccountInfo<'_>],
    data: &[u8],
) -> ProgramResult {
    match data.first().copied() {
        Some(4) => lifecycle_init(program_id, accounts, data),
        Some(5) => lifecycle_write(program_id, accounts, data),
        Some(6) => lifecycle_finalize(program_id, accounts, data),
        _ if data == &[3, 10] => stage1(program_id, accounts, data),
        _ => stage2(program_id, accounts, data),
    }
}
