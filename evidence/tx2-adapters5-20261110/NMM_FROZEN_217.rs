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
