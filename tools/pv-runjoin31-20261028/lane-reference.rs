//! Owned proof reference; frozen source is never edited.
use aspis_core::field::M31;
use aspis_statement::{poseidon2::Digest, pool_v1::{
    pair_trace::{PoolV1PairInputNoteWitnessV1, PoolV1PairTraceErrorV1}, pool_v1_tree_parent,
}};

pub fn step(current: Digest, sibling: Digest, reverse: bool) -> Digest {
    if reverse {
        pool_v1_tree_parent(&sibling, &current)
    } else {
        pool_v1_tree_parent(&current, &sibling)
    }
}

pub fn lane_root(input: PoolV1PairInputNoteWitnessV1) -> Result<Digest, PoolV1PairTraceErrorV1> {
    let mut current = input.pair_leaf.leaf_digest().map_err(PoolV1PairTraceErrorV1::PairLeaf)?;
    current = step(current, input.membership.siblings[0], ((input.membership.index >> 0u32) & 1) != 0);
    current = step(current, input.membership.siblings[1], ((input.membership.index >> 1u32) & 1) != 0);
    current = step(current, input.membership.siblings[2], ((input.membership.index >> 2u32) & 1) != 0);
    current = step(current, input.membership.siblings[3], ((input.membership.index >> 3u32) & 1) != 0);
    current = step(current, input.membership.siblings[4], ((input.membership.index >> 4u32) & 1) != 0);
    current = step(current, input.membership.siblings[5], ((input.membership.index >> 5u32) & 1) != 0);
    current = step(current, input.membership.siblings[6], ((input.membership.index >> 6u32) & 1) != 0);
    current = step(current, input.membership.siblings[7], ((input.membership.index >> 7u32) & 1) != 0);
    current = step(current, input.membership.siblings[8], ((input.membership.index >> 8u32) & 1) != 0);
    current = step(current, input.membership.siblings[9], ((input.membership.index >> 9u32) & 1) != 0);
    current = step(current, input.membership.siblings[10], ((input.membership.index >> 10u32) & 1) != 0);
    current = step(current, input.membership.siblings[11], ((input.membership.index >> 11u32) & 1) != 0);
    current = step(current, input.membership.siblings[12], ((input.membership.index >> 12u32) & 1) != 0);
    current = step(current, input.membership.siblings[13], ((input.membership.index >> 13u32) & 1) != 0);
    current = step(current, input.membership.siblings[14], ((input.membership.index >> 14u32) & 1) != 0);
    current = step(current, input.membership.siblings[15], ((input.membership.index >> 15u32) & 1) != 0);
    current = step(current, input.membership.siblings[16], ((input.membership.index >> 16u32) & 1) != 0);
    current = step(current, input.membership.siblings[17], ((input.membership.index >> 17u32) & 1) != 0);
    current = step(current, input.membership.siblings[18], ((input.membership.index >> 18u32) & 1) != 0);
    current = step(current, input.membership.siblings[19], ((input.membership.index >> 19u32) & 1) != 0);

    Ok(current)
}

// Retain the concrete field type in the extraction closure.
pub fn field_word(x: M31) -> u32 { x.0 }
