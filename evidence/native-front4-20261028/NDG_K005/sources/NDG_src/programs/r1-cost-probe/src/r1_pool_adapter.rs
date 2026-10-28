//! Default-off Pool adapter for the R1 S2 split.
//!
//! ASQ8 authentication and reconstruction are copied from the verifier's
//! `v7_pair_forest_dispatch` path. This module keeps the audit-pinned Pool,
//! registry, and policy bindings while replacing only its proof engine with
//! the R1 `tx1`/`tx2` checkpoints. Admitted routes read raw proof/public buffers
//! of any owner and use a separate verifier-owned checkpoint. Legacy lifecycle
//! helpers below are unreachable through the release entrypoint guard.

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
#[cfg(not(feature = "private-leaf-salts"))]
const PROFILE_BINDING: [u8; 32] = [
    0x78, 0x17, 0x1b, 0x56, 0x9e, 0xa7, 0xbc, 0xe5, 0x97, 0x63, 0xa2, 0xb5, 0x78, 0x81, 0x06, 0xa7,
    0x49, 0xbe, 0xd7, 0x47, 0x75, 0x6c, 0xf2, 0xd2, 0x00, 0x69, 0x99, 0x37, 0x92, 0x19, 0x13, 0xe9,
];
#[cfg(not(feature = "private-leaf-salts"))]
const RELEASE_BINDING: [u8; 32] = [
    0x45, 0x90, 0xcd, 0x06, 0x35, 0x37, 0xb3, 0xb0, 0x2f, 0xae, 0xb1, 0x0d, 0x9a, 0x7f, 0x39, 0x99,
    0x3f, 0xbe, 0x4b, 0xb6, 0x20, 0x30, 0x53, 0x32, 0x8d, 0x60, 0x0d, 0xbd, 0x48, 0x1c, 0xe0, 0x34,
];
#[cfg(feature = "private-leaf-salts")]
const PROFILE_BINDING: [u8; 32] = [
    0x57,0x94,0x73,0x13,0xd2,0x32,0x64,0x1a,0xd8,0x15,0x7d,0x66,0xbf,0xaf,0xfa,0xb1,
    0x1e,0x4c,0x3a,0x99,0x33,0x1d,0x18,0xf4,0x4b,0xfa,0xca,0xb6,0x89,0x97,0x37,0xd3,
];
#[cfg(feature = "private-leaf-salts")]
const RELEASE_BINDING: [u8; 32] = [
    0xe2,0x94,0xaf,0xbc,0x14,0xef,0x6a,0xfe,0x76,0xb8,0x47,0xde,0xf4,0x44,0x52,0xf8,
    0x4c,0xc3,0x72,0x80,0x64,0x65,0x76,0x07,0xb5,0x44,0xa5,0x39,0xca,0x9b,0x32,0x3a,
];
// Retained deployment data, never instruction immediates. The SBF linker merges
// these named input sections into .rodata; the release audit pins both slots.
#[link_section = ".rodata.aspis_pool_program_id"]
static AUDIT_POOL_PROGRAM: [u8; 32] = deployment_ids::deployment_id(
    option_env!("ASPIS_R1_POOL_PROGRAM_ID"), [0x41; 32],
);
#[link_section = ".rodata.aspis_registry_program_id"]
static AUDIT_REGISTRY_PROGRAM: [u8; 32] = deployment_ids::deployment_id(
    option_env!("ASPIS_R1_REGISTRY_PROGRAM_ID"), [0x44; 32],
);

#[inline(always)]
#[cfg_attr(kani, kani::ensures(|r| (*r == NDG_native::reference::pool_id_ref()) != cfg!(NDG_invert_pool_program_id))) ]
fn pool_program_id() -> [u8; 32] {
    *core::hint::black_box(&AUDIT_POOL_PROGRAM)
}

#[inline(always)]
#[cfg_attr(kani, kani::ensures(|r| (*r == NDG_native::reference::registry_id_ref()) != cfg!(NDG_invert_registry_program_id))) ]
fn registry_program_id() -> [u8; 32] {
    *core::hint::black_box(&AUDIT_REGISTRY_PROGRAM)
}
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
                .checked_add(verifier::PROOF_BYTES)
                .and_then(|length| length.checked_add(CHECKPOINT_TAIL_BYTES))
                .ok_or(ProgramError::InvalidAccountData),
            Self::Public => Ok(ASRU_BODY_BYTES),
        }
    }

    fn writable_prefix_len(self) -> Result<usize, ProgramError> {
        match self {
            Self::Proof => POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
                .checked_add(verifier::PROOF_BYTES)
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

#[cfg_attr(kani, kani::ensures(|r| (*r == if NDG_native::reference::readonly_ref(owner!=expected,is_signer,is_writable,executable) {Ok(())} else {Err(ProgramError::InvalidAccountData)}) != cfg!(NDG_invert_readonly_meta_ok))) ]
fn readonly_meta_ok(
    owner: &Pubkey,
    expected: &Pubkey,
    is_signer: bool,
    is_writable: bool,
    executable: bool,
) -> ProgramResult {
    if owner != expected || is_signer || is_writable || executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

fn require_readonly_account(account: &AccountInfo<'_>, owner: &Pubkey) -> ProgramResult {
    readonly_meta_ok(account.owner, owner, account.is_signer, account.is_writable, account.executable)
}

#[cfg(test)]
#[path = "readonly_meta_tests.rs"]
mod readonly_meta_tests;

#[cfg_attr(kani, kani::ensures(|r| (*r == if NDG_native::reference::readonly_buffer_ref(is_signer,is_writable,executable) {Ok(())} else {Err(ProgramError::InvalidAccountData)}) != cfg!(NDG_invert_readonly_buffer_meta_ok))) ]
fn readonly_buffer_meta_ok(
    is_signer: bool,
    is_writable: bool,
    executable: bool,
) -> ProgramResult {
    if is_signer || is_writable || executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}

fn require_readonly_buffer(account: &AccountInfo<'_>) -> ProgramResult {
    readonly_buffer_meta_ok(account.is_signer, account.is_writable, account.executable)
}

#[cfg(test)]
#[path = "readonly_buffer_tests.rs"]
mod readonly_buffer_tests;

fn require_verifier_checkpoint(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    writable: bool,
) -> ProgramResult {
    if account.owner != program_id || account.is_signer || account.executable
        || account.is_writable != writable
        || account.try_data_len()? != verifier::checkpoint_size(Variant::S2)
    {
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
            let proof_end = candidate_end + verifier::PROOF_BYTES;
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
            let variant = verifier::parse_shape(&data[candidate_end..proof_end])
                .map_err(|_| ProgramError::InvalidAccountData)?;
            if variant != Variant::S2
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
        || bytes[73..POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES]
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
        bump: bytes[72],
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
    // Versioned, owner-authenticated registry images carry the canonical bumps
    // saved by their initializers. Address checks below perform one derivation;
    // they neither search for a bump nor establish canonicality independently.
    if pool_program.to_bytes() != pool_program_id()
        || master.verifier_policy.flags & POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_REGISTRY == 0
        || master.verifier_policy.registry_program != registry_program_id()
        || master.verifier_policy.registry_authority != [0u8; 32]
        || master.verifier_policy.policy_binding != AUDIT_POLICY_BINDING
    {
        return Err(ProgramError::InvalidAccountData);
    }
    validate_verifier_policy_v1(&master.verifier_policy)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let registry_program = Pubkey::new_from_array(registry_program_id());
    require_readonly_account(registry_account, &registry_program)?;
    let immutable_deployment =
        master.verifier_policy.flags & POOL_V1_VERIFIER_POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0;
    if immutable_deployment {
        let loader = bpf_loader_upgradeable::id();
        let registry = decode_verifier_registry_v2(&registry_account.try_borrow_data()?)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        let expected_registry = Pubkey::create_program_address(
            &[
                VERIFIER_REGISTRY_V2_SEED,
                master_account.key.as_ref(),
                &[registry.bump],
            ],
            &registry_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if registry_account.key != &expected_registry {
            return Err(ProgramError::InvalidAccountData);
        }
        let registry_programdata = Pubkey::create_program_address(
            &[registry_program.as_ref(), &[registry.programdata_bump]],
            &loader,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
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
        let entry = decode_verifier_registry_entry_v2(&entry_account.try_borrow_data()?)
            .map_err(|_| ProgramError::InvalidAccountData)?;
        let expected_entry = Pubkey::create_program_address(
            &[
                VERIFIER_ENTRY_V2_SEED,
                master_account.key.as_ref(),
                &PROFILE_BINDING,
                &RELEASE_BINDING,
                &[entry.bump],
            ],
            &registry_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
        if entry_account.key != &expected_entry {
            return Err(ProgramError::InvalidAccountData);
        }
        let verifier_programdata = Pubkey::create_program_address(
            &[verifier_program.as_ref(), &[entry.programdata_bump]],
            &loader,
        )
        .map_err(|_| ProgramError::InvalidAccountData)?;
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

    let registry = decode_verifier_registry_v1(&registry_account.try_borrow_data()?)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let expected_registry = Pubkey::create_program_address(
        &[
            VERIFIER_REGISTRY_SEED,
            master_account.key.as_ref(),
            &[registry.bump],
        ],
        &registry_program,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if registry_account.key != &expected_registry {
        return Err(ProgramError::InvalidAccountData);
    }
    if registry.pool != master_account.key.to_bytes()
        || registry.authority != master.verifier_policy.registry_authority
        || registry.policy_binding != master.verifier_policy.policy_binding
        || !registry.is_immutable()
        || registry.is_paused()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    require_readonly_account(entry_account, &registry_program)?;
    let entry = decode_verifier_registry_entry_v1(&entry_account.try_borrow_data()?)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let expected_entry = Pubkey::create_program_address(
        &[
            VERIFIER_ENTRY_SEED,
            master_account.key.as_ref(),
            &PROFILE_BINDING,
            &RELEASE_BINDING,
            &[entry.bump],
        ],
        &registry_program,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;
    if entry_account.key != &expected_entry {
        return Err(ProgramError::InvalidAccountData);
    }
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
    let [proof_account, master_account, checkpoint_account, lane_account, registry_account, entry_account, verifier_checkpoint] =
        accounts
    else {
        return Err(if accounts.len() < 7 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    require_readonly_buffer(proof_account)?;
    require_verifier_checkpoint(verifier_checkpoint, verifier_program, false)?;
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
        verifier_checkpoint,
    ])?;

    let master = decode_master_box(&master_account.try_borrow_data()?)?;
    if master.identity.pool != master_account.key.to_bytes()
        || master.initialized_lane_mask != POOL_V1_PAIR_FOREST_ALL_LANES_MASK
        || Pubkey::create_program_address(
            &[
                PAIR_FOREST_MASTER_SEED,
                Pubkey::new_from_array(master.identity.asset_mint).as_ref(),
                &[master.bump],
            ],
            pool_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)? != *master_account.key
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
        || Pubkey::create_program_address(
            &[
                PAIR_FOREST_CHECKPOINT_SEED,
                master_account.key.as_ref(),
                &checkpoint.checkpoint_sequence.to_le_bytes(),
                &[checkpoint.bump],
            ],
            pool_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)? != *checkpoint_account.key
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let selected_lane = decode_lane_from_pool_release(&lane_account.try_borrow_data()?)?;
    if selected_lane.master != master_account.key.to_bytes()
        || selected_lane.lane_id != output_lane
        || Pubkey::create_program_address(
            &[
                PAIR_FOREST_LANE_SEED,
                master_account.key.as_ref(),
                &[output_lane],
                &[selected_lane.bump],
            ],
            pool_program,
        )
        .map_err(|_| ProgramError::InvalidAccountData)? != *lane_account.key
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
fn scan_proof_buffer(bytes: &[u8]) -> Result<ScannedAsqaProof, ProgramError> {
    let proof_length = verifier::PROOF_BYTES;
    let expected_body = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
        .checked_add(proof_length)
        .ok_or(ProgramError::InvalidAccountData)?;
    if bytes.len() != expected_body {
        return Err(ProgramError::InvalidAccountData);
    }
    let candidate_start = 0;
    let proof_start = candidate_start + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
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
        || request.pool_program != pool_program_id()
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
    let scanned = scan_proof_buffer(&proof_account.try_borrow_data()?)?;
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

#[path = "r1_pool_adapter_owned.rs"]
mod owned;
use owned::{stage1, stage2};

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
        _ if data == &[3, 10] || data == &[3, 11] => stage1(program_id, accounts, data),
        _ => stage2(program_id, accounts, data),
    }
}

#[cfg(all(test, feature = "private-leaf-salts"))]
#[path = "r1_checkpoint_tests.rs"]
mod checkpoint_tests;

#[path = "deployment_ids.rs"]
mod deployment_ids;

#[cfg(all(test, feature = "private-leaf-salts"))]
#[path = "adapter_rw_tests.rs"]
mod rw_tests;

#[cfg(kani)]
#[path="NDG_native.rs"]
mod NDG_native;
