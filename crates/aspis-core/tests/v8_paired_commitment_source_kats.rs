//! Research-only R8 source KATs. These bind the low-level V7 hash grammar and
//! shared-topology verifier, not the selected V8 payload serializer or caller.

use aspis_core::v7_merkle208::{
    node_hash_v7, private_leaf_hash_v7, truncate_sha256_v7, verify_two_minimal_subtrees_v7_bytes,
    V7Digest, V7_C1_TREE_TAG, V7_C2_TREE_TAG, V7_MERKLE_DIGEST_BYTES,
};
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;

fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for part in parts {
        h.update(part);
    }
    h.finalize().into()
}

#[test]
fn r8_literal_tags_and_leaf_grammar() {
    assert_eq!((V7_C1_TREE_TAG, V7_C2_TREE_TAG), (0x71, 0xf1));
    assert_eq!(V7_MERKLE_DIGEST_BYTES, 26);
    let salt = [7u8; 32];
    for tag in [V7_C1_TREE_TAG, V7_C2_TREE_TAG] {
        let payload = b"opaque-source-wrapper-test";
        let direct = hash(&[&[0x10, tag], payload, &salt]);
        assert_eq!(
            private_leaf_hash_v7(hash, tag, payload, &salt),
            truncate_sha256_v7(direct)
        );
    }
}

#[test]
fn r8_node_uses_exact_53_byte_untagged_input() {
    let left = [11u8; 26];
    let right = [13u8; 26];
    assert_eq!(
        node_hash_v7(hash, &left, &right),
        truncate_sha256_v7(hash(&[&[0x11], &left, &right]))
    );
}

fn build(tag: u8) -> Vec<Vec<V7Digest>> {
    let mut levels = vec![(0..8u8)
        .map(|index| private_leaf_hash_v7(hash, tag, &[index, tag, 42], &[index + 1; 32]))
        .collect::<Vec<_>>()];
    while levels.last().unwrap().len() > 1 {
        let children = levels.last().unwrap();
        let parents = children
            .chunks_exact(2)
            .map(|pair| node_hash_v7(hash, &pair[0], &pair[1]))
            .collect();
        levels.push(parents);
    }
    levels
}

fn frontier(tree: &[Vec<V7Digest>], indices: &[u32]) -> Vec<u8> {
    let mut live: BTreeSet<u32> = indices.iter().copied().collect();
    let mut bytes = Vec::new();
    for layer in &tree[..tree.len() - 1] {
        for index in &live {
            if !live.contains(&(*index ^ 1)) {
                bytes.extend_from_slice(&layer[(*index ^ 1) as usize]);
            }
        }
        live = live.iter().map(|index| *index >> 1).collect();
    }
    bytes
}

#[test]
fn r8_all_255_small_shared_frontiers_use_actual_verifier() {
    let c1 = build(V7_C1_TREE_TAG);
    let c2 = build(V7_C2_TREE_TAG);
    for selection in 1u32..256 {
        let indices: Vec<u32> = (0u32..8)
            .filter(|index| selection & (1 << index) != 0)
            .collect();
        let entries: Vec<_> = indices
            .iter()
            .map(|&index| (index, c1[0][index as usize], c2[0][index as usize]))
            .collect();
        let c1_frontier = frontier(&c1, &indices);
        let c2_frontier = frontier(&c2, &indices);
        assert_eq!(c1_frontier.len(), c2_frontier.len());
        assert!(verify_two_minimal_subtrees_v7_bytes(
            hash,
            (&c1[3][0], &c2[3][0]),
            3,
            &entries,
            (&c1_frontier, &c2_frontier),
            &mut Vec::new(),
            &mut Vec::new()
        ));
        let mut extra = c1_frontier.clone();
        extra.extend_from_slice(&[99; 26]);
        assert!(!verify_two_minimal_subtrees_v7_bytes(
            hash,
            (&c1[3][0], &c2[3][0]),
            3,
            &entries,
            (&extra, &c2_frontier),
            &mut Vec::new(),
            &mut Vec::new()
        ));
    }
}
