#![allow(dead_code)]
pub const POOL_V1_PAIR_TREE_DEPTH: usize = 20;
pub type Digest = [M31; 8];


/// M31 base field element, canonical representation in [0, P).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);


/// Spend shapes that consume an authenticated historical anchor.
///
/// Zero is deliberately invalid.  Deposit is absent because it consumes no
/// private input and therefore must never authorize through this envelope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum PoolV1TransitionKind {
    PrivateTransfer = 1,
    Withdrawal = 2,
}


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PrivateTransferPublicV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: Digest,
    pub nullifier: Digest,
    pub asset_id: M31,
    pub recipient_commitment: Digest,
    pub change_commitment: Digest,
}


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1WithdrawalPublicV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub anchor_sequence: u64,
    pub anchor_root: Digest,
    pub nullifier: Digest,
    pub asset_id: M31,
    pub amount: u32,
    pub destination_token_account: [u8; 32],
    pub change_commitment: Digest,
}


/// Minimal proof-carried append result for the one-terminal transaction.
///
/// This is not the execution-time append experiment above.  The selected
/// verifier has checked the twenty late Poseidon parents against the exact
/// live snapshot and returns the resulting state.  The Pool performs only
/// canonical byte validation, checks `next_pair_index = current + 1`, and
/// persists these bytes atomically with history and the nullifier marker.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairVerifiedAfterstateV1 {
    pub next_pair_index: u64,
    pub next_root: Digest,
    pub next_frontier: [Digest; POOL_V1_PAIR_TREE_DEPTH],
}


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairLiveSnapshotV1 {
    pub pool: [u8; 32],
    pub deployment_domain: [u8; 32],
    pub sequence: u64,
    pub next_pair_index: u64,
    pub current_root: Digest,
    pub frontier: [Digest; POOL_V1_PAIR_TREE_DEPTH],
}


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairLatePublicStatementV1 {
    pub live_snapshot: PoolV1PairLiveSnapshotV1,
    /// One appended pair advances the pair index by one even though a private
    /// transfer fills two commitment slots (note indices `2i` and `2i+1`).
    pub candidate_afterstate: PoolV1PairVerifiedAfterstateV1,
}


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestTerminalCommonV1 {
    pub master_account: [u8; 32],
    pub checkpoint_account: [u8; 32],
    pub selected_lane_account: [u8; 32],
    pub output_lane: u8,
    pub checkpoint_sequence: u64,
    /// Historical global membership anchor reconstructed at trace block 56.
    pub historical_global_anchor: Digest,
    /// Exact selected-output-lane beforestate and candidate afterstate.
    pub lane_transition: PoolV1PairLatePublicStatementV1,
}


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1PairForestTerminalStatementV1 {
    PrivateTransfer {
        common: PoolV1PairForestTerminalCommonV1,
        public: PoolV1PrivateTransferPublicV1,
    },
    Withdrawal {
        common: PoolV1PairForestTerminalCommonV1,
        public: PoolV1WithdrawalPublicV1,
    },
}


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestTerminalResultV1 {
    pub transition_kind: PoolV1TransitionKind,
    pub master_account: [u8; 32],
    pub selected_lane_account: [u8; 32],
    pub output_lane: u8,
    pub nullifier: Digest,
    pub verified_afterstate: PoolV1PairVerifiedAfterstateV1,
}

impl PoolV1PairForestTerminalStatementV1 {
pub fn common(&self) -> &PoolV1PairForestTerminalCommonV1 {
        match self {
            Self::PrivateTransfer { common, .. } | Self::Withdrawal { common, .. } => common,
        }
    }
pub fn transition_kind(&self) -> PoolV1TransitionKind {
        match self {
            Self::PrivateTransfer { .. } => PoolV1TransitionKind::PrivateTransfer,
            Self::Withdrawal { .. } => PoolV1TransitionKind::Withdrawal,
        }
    }
pub fn nullifier(&self) -> &Digest {
        match self {
            Self::PrivateTransfer { public, .. } => &public.nullifier,
            Self::Withdrawal { public, .. } => &public.nullifier,
        }
    }
}

pub fn emitted_result_value(statement: &PoolV1PairForestTerminalStatementV1) -> PoolV1PairForestTerminalResultV1 {
    let result = PoolV1PairForestTerminalResultV1 {
        transition_kind: statement.transition_kind(),
        master_account: statement.common().master_account,
        selected_lane_account: statement.common().selected_lane_account,
        output_lane: statement.common().output_lane,
        nullifier: *statement.nullifier(),
        verified_afterstate: statement.common().lane_transition.candidate_afterstate,
    };
    result
}

impl M31 {
pub fn to_le_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
}
pub fn encode_digest_canonical(digest: &Digest) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (index, value) in digest.iter().enumerate() {
        bytes[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
    }
    bytes
}
pub const POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC: [u8;
pub const POOL_V1_PAIR_FOREST_TERMINAL_VERSION: u8 = 1;
pub const POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES: usize =
    8 + 3 * 32 + POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
const RESULT_MASTER_OFFSET: usize = 8;
const RESULT_SELECTED_LANE_OFFSET: usize = 40;
const RESULT_NULLIFIER_OFFSET: usize = 72;
const RESULT_AFTERSTATE_OFFSET: usize = 104;
const POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES: usize = 688;
const POOL_V1_DIGEST_ENCODING_VERSION: u8 = 1;

pub fn encode_fields(result: &PoolV1PairForestTerminalResultV1, afterstate: &[u8;688]) -> [u8;792] {
    let mut output = [0u8; POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC);
    output[4] = POOL_V1_PAIR_FOREST_TERMINAL_VERSION;
    output[5] = result.transition_kind as u8;
    output[6] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[7] = result.output_lane;
    output[RESULT_MASTER_OFFSET..RESULT_SELECTED_LANE_OFFSET]
        .copy_from_slice(&result.master_account);
    output[RESULT_SELECTED_LANE_OFFSET..RESULT_NULLIFIER_OFFSET]
        .copy_from_slice(&result.selected_lane_account);
    output[RESULT_NULLIFIER_OFFSET..RESULT_AFTERSTATE_OFFSET]
        .copy_from_slice(&encode_digest_canonical(&result.nullifier));
    output[RESULT_AFTERSTATE_OFFSET..].copy_from_slice(afterstate);
    output
}
