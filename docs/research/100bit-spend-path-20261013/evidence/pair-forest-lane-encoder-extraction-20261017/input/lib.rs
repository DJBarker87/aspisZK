#![allow(dead_code)]

pub const POOL_V1_TREE_DEPTH: usize = 20;
pub const POOL_V1_PAIR_TREE_DEPTH: usize = 20;
pub const POOL_V1_PAIR_FOREST_LANE_COUNT: usize = 8;
pub const POOL_V1_PAIR_CAPACITY: u64 = 1u64 << POOL_V1_PAIR_TREE_DEPTH;
pub const POOL_V1_PAIR_FOREST_LANE_HEADER_BYTES: usize = 80;
pub const POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES: usize = 768;
pub const POOL_V1_PAIR_FOREST_LANE_MAGIC: [u8; 4] = *b"ASL8";
pub const POOL_V1_PAIR_FOREST_LANE_VERSION: u8 = 2;
pub const POOL_V1_TREE_STATE_MAGIC: [u8; 4] = *b"ASPT";
pub const POOL_V1_TREE_STATE_VERSION: u8 = 1;
pub const POOL_V1_TREE_HASH_VERSION: u8 = 3;
pub const POOL_V1_DIGEST_ENCODING_VERSION: u8 = 1;

/// This literal is copied from pair_forest_accounts.rs and is the dedicated
/// eight-lane account format binding.
pub const POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING: [u8; 32] = [
    b'A', b'S', b'P', b'I', b'S', b'F', b'O', b'R', b'E', b'S', b'T', b'8',
    2, 2, 2, 8, 1, 20, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
];

#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);

impl M31 {
    pub const fn to_le_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }
}

pub type Digest = [M31; 8];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1ProgramError { StateHistoryMismatch }
pub type ProgramError = PoolV1ProgramError;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IncrementalMerkleTreeV1 {
    pub next_leaf_index: u64,
    pub root: Digest,
    pub frontier: [Digest; POOL_V1_TREE_DEPTH],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoolV1PairForestLaneStateV1 {
    pub bump: u8,
    pub master: [u8; 32],
    pub lane_id: u8,
    pub tree: IncrementalMerkleTreeV1,
}

#[inline]
pub fn encode_digest_canonical(digest: &Digest) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    bytes[0..4].copy_from_slice(&digest[0].to_le_bytes());
    bytes[4..8].copy_from_slice(&digest[1].to_le_bytes());
    bytes[8..12].copy_from_slice(&digest[2].to_le_bytes());
    bytes[12..16].copy_from_slice(&digest[3].to_le_bytes());
    bytes[16..20].copy_from_slice(&digest[4].to_le_bytes());
    bytes[20..24].copy_from_slice(&digest[5].to_le_bytes());
    bytes[24..28].copy_from_slice(&digest[6].to_le_bytes());
    bytes[28..32].copy_from_slice(&digest[7].to_le_bytes());
    bytes
}

/// Exact body from programs/aspis-pool/src/pair_forest.rs, lines 460–505.
pub fn encode_lane_from_authenticated_result_v1(
    lane: &PoolV1PairForestLaneStateV1,
    pair_empty_roots: &[Digest; POOL_V1_PAIR_TREE_DEPTH + 1],
) -> Result<[u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES], ProgramError> {
    if usize::from(lane.lane_id) >= POOL_V1_PAIR_FOREST_LANE_COUNT
        || lane.master == [0u8; 32]
        || lane.tree.next_leaf_index > POOL_V1_PAIR_CAPACITY
    {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    if (lane.tree.next_leaf_index >> 0) & 1 == 0 && lane.tree.frontier[0] != pair_empty_roots[0] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 1) & 1 == 0 && lane.tree.frontier[1] != pair_empty_roots[1] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 2) & 1 == 0 && lane.tree.frontier[2] != pair_empty_roots[2] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 3) & 1 == 0 && lane.tree.frontier[3] != pair_empty_roots[3] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 4) & 1 == 0 && lane.tree.frontier[4] != pair_empty_roots[4] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 5) & 1 == 0 && lane.tree.frontier[5] != pair_empty_roots[5] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 6) & 1 == 0 && lane.tree.frontier[6] != pair_empty_roots[6] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 7) & 1 == 0 && lane.tree.frontier[7] != pair_empty_roots[7] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 8) & 1 == 0 && lane.tree.frontier[8] != pair_empty_roots[8] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 9) & 1 == 0 && lane.tree.frontier[9] != pair_empty_roots[9] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 10) & 1 == 0 && lane.tree.frontier[10] != pair_empty_roots[10] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 11) & 1 == 0 && lane.tree.frontier[11] != pair_empty_roots[11] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 12) & 1 == 0 && lane.tree.frontier[12] != pair_empty_roots[12] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 13) & 1 == 0 && lane.tree.frontier[13] != pair_empty_roots[13] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 14) & 1 == 0 && lane.tree.frontier[14] != pair_empty_roots[14] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 15) & 1 == 0 && lane.tree.frontier[15] != pair_empty_roots[15] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 16) & 1 == 0 && lane.tree.frontier[16] != pair_empty_roots[16] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 17) & 1 == 0 && lane.tree.frontier[17] != pair_empty_roots[17] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 18) & 1 == 0 && lane.tree.frontier[18] != pair_empty_roots[18] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if (lane.tree.next_leaf_index >> 19) & 1 == 0 && lane.tree.frontier[19] != pair_empty_roots[19] { return Err(PoolV1ProgramError::StateHistoryMismatch.into()); }
    if lane.tree.next_leaf_index == 0
        && lane.tree.root != pair_empty_roots[POOL_V1_TREE_DEPTH]
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
    output[80..84].copy_from_slice(&POOL_V1_TREE_STATE_MAGIC);
    output[84] = POOL_V1_TREE_STATE_VERSION;
    output[85] = POOL_V1_PAIR_TREE_DEPTH as u8;
    output[86] = POOL_V1_TREE_HASH_VERSION;
    output[87] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[88..96].copy_from_slice(&lane.tree.next_leaf_index.to_le_bytes());
    output[96..128].copy_from_slice(&encode_digest_canonical(&lane.tree.root));
    output[128..160].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[0]));
    output[160..192].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[1]));
    output[192..224].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[2]));
    output[224..256].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[3]));
    output[256..288].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[4]));
    output[288..320].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[5]));
    output[320..352].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[6]));
    output[352..384].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[7]));
    output[384..416].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[8]));
    output[416..448].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[9]));
    output[448..480].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[10]));
    output[480..512].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[11]));
    output[512..544].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[12]));
    output[544..576].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[13]));
    output[576..608].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[14]));
    output[608..640].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[15]));
    output[640..672].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[16]));
    output[672..704].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[17]));
    output[704..736].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[18]));
    output[736..768].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[19]));
    Ok(output)
}


/// Exact source-tail cut: production output construction after validation.
pub fn encode_lane_bytes_tail_v1(
    lane: &PoolV1PairForestLaneStateV1,
) -> [u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES] {
    let mut output = [0u8; POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES];
    output[..4].copy_from_slice(&POOL_V1_PAIR_FOREST_LANE_MAGIC);
    output[4] = POOL_V1_PAIR_FOREST_LANE_VERSION;
    output[5] = lane.lane_id;
    output[6] = POOL_V1_PAIR_FOREST_LANE_COUNT as u8;
    output[7] = POOL_V1_PAIR_TREE_DEPTH as u8;
    output[8..40].copy_from_slice(&POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING);
    output[40..72].copy_from_slice(&lane.master);
    output[72] = lane.bump;
    output[80..84].copy_from_slice(&POOL_V1_TREE_STATE_MAGIC);
    output[84] = POOL_V1_TREE_STATE_VERSION;
    output[85] = POOL_V1_PAIR_TREE_DEPTH as u8;
    output[86] = POOL_V1_TREE_HASH_VERSION;
    output[87] = POOL_V1_DIGEST_ENCODING_VERSION;
    output[88..96].copy_from_slice(&lane.tree.next_leaf_index.to_le_bytes());
    output[96..128].copy_from_slice(&encode_digest_canonical(&lane.tree.root));
    output[128..160].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[0]));
    output[160..192].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[1]));
    output[192..224].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[2]));
    output[224..256].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[3]));
    output[256..288].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[4]));
    output[288..320].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[5]));
    output[320..352].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[6]));
    output[352..384].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[7]));
    output[384..416].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[8]));
    output[416..448].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[9]));
    output[448..480].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[10]));
    output[480..512].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[11]));
    output[512..544].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[12]));
    output[544..576].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[13]));
    output[576..608].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[14]));
    output[608..640].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[15]));
    output[640..672].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[16]));
    output[672..704].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[17]));
    output[704..736].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[18]));
    output[736..768].copy_from_slice(&encode_digest_canonical(&lane.tree.frontier[19]));
    output
}
