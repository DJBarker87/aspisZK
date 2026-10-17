#![allow(dead_code)]
use core::convert::From;

pub const POOL_V1_TREE_DEPTH: usize = 20;
pub const POOL_V1_PAIR_TREE_DEPTH: usize = 20;
pub type Digest = [M31; 8];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1ProgramError { StateHistoryMismatch }
pub type ProgramError = PoolV1ProgramError;


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
pub struct IncrementalMerkleTreeV1 {
    pub next_leaf_index: u64,
    pub root: Digest,
    pub frontier: [Digest; POOL_V1_TREE_DEPTH],
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
pub struct PoolV1PairForestLaneStateV1 {
    /// Canonical PDA bump persisted by Pool initialization (wire byte 72).
    pub bump: u8,
    pub master: [u8; 32],
    pub lane_id: u8,
    pub tree: IncrementalMerkleTreeV1,
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



fn next_pair_forest_lane_v1(
    lane: &PoolV1PairForestLaneStateV1,
    pair_empty_roots: &[Digest; POOL_V1_PAIR_TREE_DEPTH + 1],
    result: &PoolV1PairForestTerminalResultV1,
) -> Result<PoolV1PairForestLaneStateV1, ProgramError> {
    let afterstate = result.verified_afterstate;
    if lane.tree.next_leaf_index.checked_add(1) != Some(afterstate.next_pair_index) {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    for (level, node) in afterstate.next_frontier.iter().enumerate() {
        if (afterstate.next_pair_index >> level) & 1 == 0
            && *node != pair_empty_roots[level]
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


