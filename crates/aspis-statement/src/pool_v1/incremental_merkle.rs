//! Pure append-only Pool V1 Merkle frontier.
//!
//! The state uses the conventional binary carry frontier.  Slot `h` is live
//! exactly when bit `h` of `next_leaf_index` is one.  Inactive slots are
//! canonical recursive empty roots, so a serialized state has one byte image.
//! All operations validate first and return a new state; errors cannot expose
//! a partially updated frontier.

use aspis_core::field::M31;

use crate::{
    decode_digest_canonical, encode_digest_canonical,
    poseidon2::{Digest, DIGEST_ELEMS},
};

use super::{
    format::{
        pool_v1_tree_parent, POOL_V1_DIGEST_ENCODING_VERSION, POOL_V1_TREE_DEPTH,
        POOL_V1_TREE_HASH_VERSION,
    },
    root_history::{root_history_location, RootHistoryLocationV1},
};

pub const POOL_V1_TREE_STATE_MAGIC: [u8; 4] = *b"ASPT";
pub const POOL_V1_TREE_STATE_VERSION: u8 = 1;
pub const POOL_V1_LEAF_CAPACITY: u64 = 1u64 << POOL_V1_TREE_DEPTH;
pub const POOL_V1_TREE_STATE_HEADER_BYTES: usize = 48;
pub const POOL_V1_TREE_STATE_ACCOUNT_BYTES: usize =
    POOL_V1_TREE_STATE_HEADER_BYTES + 32 * POOL_V1_TREE_DEPTH;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PoolV1TreeError {
    TreeFull,
    InsufficientCapacity,
    IndexOutOfRange,
    RootMismatch,
    NonCanonicalFrontier,
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongDepth,
    WrongTreeHash,
    WrongDigestEncoding,
    NonCanonicalDigest,
    NonZeroReserved,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AppendOneV1 {
    pub leaf_index: u64,
    /// Root sequence zero is the empty root, hence sequence = index + 1.
    pub root_sequence: u64,
    pub root: Digest,
    pub history: RootHistoryLocationV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AppendTwoV1 {
    pub first: AppendOneV1,
    pub second: AppendOneV1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IncrementalMerkleTreeV1 {
    pub next_leaf_index: u64,
    pub root: Digest,
    pub frontier: [Digest; POOL_V1_TREE_DEPTH],
}

/// A tree paired with the exact empty-root table against which its complete
/// frontier/root invariant was checked.
///
/// The inner tree and table binding are private. Callers can obtain this
/// capability only through a validating constructor, while append operations
/// return a new capability by the checked carry construction itself. This
/// permits trusted integration code to avoid reconstructing the same source
/// and result roots more than once without exposing an unchecked append API.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValidatedIncrementalMerkleTreeV1<'a> {
    inner: IncrementalMerkleTreeV1,
    empty: &'a [Digest; POOL_V1_TREE_DEPTH + 1],
}

pub fn pool_v1_empty_roots() -> [Digest; POOL_V1_TREE_DEPTH + 1] {
    let mut roots = [[M31::ZERO; DIGEST_ELEMS]; POOL_V1_TREE_DEPTH + 1];
    for level in 0..POOL_V1_TREE_DEPTH {
        roots[level + 1] = pool_v1_tree_parent(&roots[level], &roots[level]);
    }
    roots
}

fn decode_tree_image_unvalidated(bytes: &[u8]) -> Result<IncrementalMerkleTreeV1, PoolV1TreeError> {
    if bytes.len() != POOL_V1_TREE_STATE_ACCOUNT_BYTES {
        return Err(PoolV1TreeError::WrongLength);
    }
    if bytes[..4] != POOL_V1_TREE_STATE_MAGIC {
        return Err(PoolV1TreeError::WrongMagic);
    }
    if bytes[4] != POOL_V1_TREE_STATE_VERSION {
        return Err(PoolV1TreeError::WrongVersion);
    }
    if bytes[5] != POOL_V1_TREE_DEPTH as u8 {
        return Err(PoolV1TreeError::WrongDepth);
    }
    if bytes[6] != POOL_V1_TREE_HASH_VERSION {
        return Err(PoolV1TreeError::WrongTreeHash);
    }
    if bytes[7] != POOL_V1_DIGEST_ENCODING_VERSION {
        return Err(PoolV1TreeError::WrongDigestEncoding);
    }
    let next_leaf_index = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
    let root = decode_digest_canonical(bytes[16..48].try_into().unwrap())
        .map_err(|_| PoolV1TreeError::NonCanonicalDigest)?;
    // A `while` loop with a flag instead of `iter_mut().enumerate()` with `?` inside; it
    // stops at the first non-canonical level and returns the same error after the loop.
    let mut frontier = [[M31::ZERO; DIGEST_ELEMS]; POOL_V1_TREE_DEPTH];
    let mut canonical = true;
    let mut level = 0;
    while canonical && level < POOL_V1_TREE_DEPTH {
        let start = POOL_V1_TREE_STATE_HEADER_BYTES + level * 32;
        match decode_digest_canonical(bytes[start..start + 32].try_into().unwrap()) {
            Ok(node) => frontier[level] = node,
            Err(_) => canonical = false,
        }
        level += 1;
    }
    if !canonical {
        return Err(PoolV1TreeError::NonCanonicalDigest);
    }
    Ok(IncrementalMerkleTreeV1 {
        next_leaf_index,
        root,
        frontier,
    })
}

/// The body of `ValidatedIncrementalMerkleTreeV1::append_one` (frozen commit 3d700effcabe) over plain values;
/// the shift amounts as u32 (the native `wrapping_shr` takes u32; same values).
fn append_one_core_v1(
    leaf_index: u64,
    source_frontier: [Digest; POOL_V1_TREE_DEPTH],
    leaf: Digest,
    empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
) -> Result<(IncrementalMerkleTreeV1, AppendOneV1), PoolV1TreeError> {
    if leaf_index == POOL_V1_LEAF_CAPACITY {
        return Err(PoolV1TreeError::TreeFull);
    }
    let mut frontier = source_frontier;
    let mut carry = leaf;
    let mut carry_level = 0usize;
    while carry_level < POOL_V1_TREE_DEPTH && (leaf_index >> (carry_level as u32)) & 1 == 1 {
        carry = pool_v1_tree_parent(&frontier[carry_level], &carry);
        frontier[carry_level] = empty[carry_level];
        carry_level += 1;
    }
    let next_leaf_index = leaf_index + 1;
    let root = if carry_level == POOL_V1_TREE_DEPTH {
        carry
    } else {
        frontier[carry_level] = carry;
        let provisional = IncrementalMerkleTreeV1 {
            next_leaf_index,
            root: [M31::ZERO; DIGEST_ELEMS],
            frontier,
        };
        match provisional.reconstruct_nonfull_root_from_level(empty, carry_level) {
            Ok(root) => root,
            Err(err) => return Err(err),
        }
    };
    let receipt = AppendOneV1 {
        leaf_index,
        root_sequence: next_leaf_index,
        root,
        history: root_history_location(next_leaf_index),
    };
    Ok((
        IncrementalMerkleTreeV1 {
            next_leaf_index,
            root,
            frontier,
        },
        receipt,
    ))
}

impl<'a> ValidatedIncrementalMerkleTreeV1<'a> {
    /// Construct sequence zero and perform the same complete validation used
    /// by `from_parts` before minting the capability.
    pub fn empty(empty: &'a [Digest; POOL_V1_TREE_DEPTH + 1]) -> Result<Self, PoolV1TreeError> {
        Self::from_parts(
            0,
            empty[POOL_V1_TREE_DEPTH],
            core::array::from_fn(|level| empty[level]),
            empty,
        )
    }

    /// Validate one raw tree exactly once against the supplied authenticated
    /// empty-root table, then seal the result together with that table.
    pub fn from_parts(
        next_leaf_index: u64,
        root: Digest,
        frontier: [Digest; POOL_V1_TREE_DEPTH],
        empty: &'a [Digest; POOL_V1_TREE_DEPTH + 1],
    ) -> Result<Self, PoolV1TreeError> {
        let inner = IncrementalMerkleTreeV1 {
            next_leaf_index,
            root,
            frontier,
        };
        inner.validate_with_empty_roots(empty)?;
        Ok(Self { inner, empty })
    }

    /// Strictly decode the frozen tree image, perform its complete invariant
    /// check once, and seal both the tree and table binding.
    pub fn decode(
        bytes: &[u8],
        empty: &'a [Digest; POOL_V1_TREE_DEPTH + 1],
    ) -> Result<Self, PoolV1TreeError> {
        let inner = decode_tree_image_unvalidated(bytes)?;
        Self::from_parts(inner.next_leaf_index, inner.root, inner.frontier, empty)
    }

    pub fn as_tree(&self) -> &IncrementalMerkleTreeV1 {
        &self.inner
    }

    pub fn into_inner(self) -> IncrementalMerkleTreeV1 {
        self.inner
    }

    /// Append to an already-validated source without reconstructing its root.
    ///
    /// The carry/frontier update is identical to the plain API. For a
    /// non-full result, `reconstruct_nonfull_root` is the one required new-root
    /// computation. Canonical inactive slots follow by construction from the
    /// validated source and the explicit clearing/carry-stop assignments, so
    /// the returned sealed result needs no second root reconstruction.
    pub fn append_one(&self, leaf: Digest) -> Result<(Self, AppendOneV1), PoolV1TreeError> {
        // Translatable form (the tools reject: joining region abstractions with shared loans that contain borrows): the body runs
        // in `append_one_core_v1` over plain values and the pinned table; the capability is rebuilt around its
        // result with the same table. Same checks, parents and receipt.
        let (inner, receipt) =
            match append_one_core_v1(self.inner.next_leaf_index, self.inner.frontier, leaf, self.empty) {
                Ok(value) => value,
                Err(err) => return Err(err),
            };
        Ok((Self { inner, empty: self.empty }, receipt))
    }

    /// Atomically append two leaves using the same sealed-table capability.
    pub fn append_two(
        &self,
        first_leaf: Digest,
        second_leaf: Digest,
    ) -> Result<(Self, AppendTwoV1), PoolV1TreeError> {
        if POOL_V1_LEAF_CAPACITY
            .checked_sub(self.inner.next_leaf_index)
            .ok_or(PoolV1TreeError::IndexOutOfRange)?
            < 2
        {
            return Err(PoolV1TreeError::InsufficientCapacity);
        }
        let (after_first, first) = self.append_one(first_leaf)?;
        let (after_second, second) = after_first.append_one(second_leaf)?;
        Ok((after_second, AppendTwoV1 { first, second }))
    }
}

impl core::ops::Deref for ValidatedIncrementalMerkleTreeV1<'_> {
    type Target = IncrementalMerkleTreeV1;

    fn deref(&self) -> &Self::Target {
        self.as_tree()
    }
}

impl IncrementalMerkleTreeV1 {
    pub fn empty() -> Self {
        let empty = pool_v1_empty_roots();
        Self {
            next_leaf_index: 0,
            root: empty[POOL_V1_TREE_DEPTH],
            frontier: core::array::from_fn(|level| empty[level]),
        }
    }

    pub fn from_parts(
        next_leaf_index: u64,
        root: Digest,
        frontier: [Digest; POOL_V1_TREE_DEPTH],
    ) -> Result<Self, PoolV1TreeError> {
        let empty = pool_v1_empty_roots();
        Self::from_parts_with_empty_roots(next_leaf_index, root, frontier, &empty)
    }

    /// Construct and validate against a caller-authenticated empty-root table.
    ///
    /// Pool SBF code uses a pinned, KAT-checked table to avoid recomputing 20
    /// Poseidon nodes on every validation. Supplying an unauthenticated table
    /// would change the tree semantics and is therefore a source boundary.
    pub fn from_parts_with_empty_roots(
        next_leaf_index: u64,
        root: Digest,
        frontier: [Digest; POOL_V1_TREE_DEPTH],
        empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
    ) -> Result<Self, PoolV1TreeError> {
        ValidatedIncrementalMerkleTreeV1::from_parts(next_leaf_index, root, frontier, empty)
            .map(ValidatedIncrementalMerkleTreeV1::into_inner)
    }

    pub fn remaining_capacity(&self) -> Result<u64, PoolV1TreeError> {
        POOL_V1_LEAF_CAPACITY
            .checked_sub(self.next_leaf_index)
            .ok_or(PoolV1TreeError::IndexOutOfRange)
    }

    pub fn validate(&self) -> Result<(), PoolV1TreeError> {
        let empty = pool_v1_empty_roots();
        self.validate_with_empty_roots(&empty)
    }

    pub fn validate_with_empty_roots(
        &self,
        empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
    ) -> Result<(), PoolV1TreeError> {
        if self.next_leaf_index > POOL_V1_LEAF_CAPACITY {
            return Err(PoolV1TreeError::IndexOutOfRange);
        }
        // Translatable form (the tools reject: "unexpected return"): a `while` loop with a flag instead of a return inside the
        // loop (same first failing level, same error), and the sequence-zero result without a `return if`
        // expression. Shift amounts as u32 (same values).
        let mut canonical = true;
        let mut level = 0;
        while canonical && level < POOL_V1_TREE_DEPTH {
            canonical = (self.next_leaf_index >> (level as u32)) & 1 != 0 || self.frontier[level] == empty[level];
            level += 1;
        }
        if !canonical {
            return Err(PoolV1TreeError::NonCanonicalFrontier);
        }
        // Sequence zero has one exact canonical image: every frontier slot is
        // the corresponding pinned recursive empty root (checked above), and
        // the explicit root is the pinned depth-D empty root.  Recomputing the
        // same twenty Poseidon parents here proves no additional relation and
        // is prohibitively expensive in the Pool's preparation instruction.
        if self.next_leaf_index == 0 {
            if self.root != empty[POOL_V1_TREE_DEPTH] {
                return Err(PoolV1TreeError::RootMismatch);
            }
            return Ok(());
        }
        // A full tree has carried beyond the last stored frontier slot.  Its
        // canonical frontier is empty and its terminal root remains explicit
        // in `root`; no further append is permitted.  Every non-full state is
        // reconstructible from its live frontier and recursive empty roots.
        //
        // Consequently, this account image alone cannot prove the provenance
        // of a depth-D terminal root.  Program integration must only create a
        // full state through the final append and, when loading it again,
        // cross-check `root` against sequence 2^D in the deterministic root
        // history.  `validate_terminal_root_against_history` performs the
        // compact cross-check without adding a terminal witness to this
        // frozen 688-byte layout.
        if self.next_leaf_index < POOL_V1_LEAF_CAPACITY
            && self.reconstruct_nonfull_root(empty)? != self.root
        {
            return Err(PoolV1TreeError::RootMismatch);
        }
        Ok(())
    }

    /// Check the otherwise-unreconstructible full-tree root against history.
    ///
    /// The retained root must come from the deterministic history location
    /// `root_history_location(POOL_V1_LEAF_CAPACITY)`.  The caller remains
    /// responsible for authenticating the Pool V1 root-history account.
    pub fn validate_terminal_root_against_history(
        &self,
        retained_root: &Digest,
    ) -> Result<(), PoolV1TreeError> {
        let empty = pool_v1_empty_roots();
        self.validate_terminal_root_against_history_with_empty_roots(retained_root, &empty)
    }

    pub fn validate_terminal_root_against_history_with_empty_roots(
        &self,
        retained_root: &Digest,
        empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
    ) -> Result<(), PoolV1TreeError> {
        self.validate_with_empty_roots(empty)?;
        if self.next_leaf_index != POOL_V1_LEAF_CAPACITY {
            return Err(PoolV1TreeError::IndexOutOfRange);
        }
        if self.root != *retained_root {
            return Err(PoolV1TreeError::RootMismatch);
        }
        Ok(())
    }

    fn reconstruct_nonfull_root(
        &self,
        empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
    ) -> Result<Digest, PoolV1TreeError> {
        self.reconstruct_nonfull_root_from_level(empty, 0)
    }

    fn reconstruct_nonfull_root_from_level(
        &self,
        empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
        start_level: usize,
    ) -> Result<Digest, PoolV1TreeError> {
        if self.next_leaf_index >= POOL_V1_LEAF_CAPACITY {
            return Err(PoolV1TreeError::TreeFull);
        }
        if start_level > POOL_V1_TREE_DEPTH {
            return Err(PoolV1TreeError::IndexOutOfRange);
        }
        let mut node = empty[start_level];
        for level in start_level..POOL_V1_TREE_DEPTH {
            node = if (self.next_leaf_index >> (level as u32)) & 1 == 0 {
                pool_v1_tree_parent(&node, &empty[level])
            } else {
                pool_v1_tree_parent(&self.frontier[level], &node)
            };
        }
        Ok(node)
    }

    pub fn append_one(&self, leaf: Digest) -> Result<(Self, AppendOneV1), PoolV1TreeError> {
        let empty = pool_v1_empty_roots();
        self.append_one_with_empty_roots(leaf, &empty)
    }

    pub fn append_one_with_empty_roots(
        &self,
        leaf: Digest,
        empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
    ) -> Result<(Self, AppendOneV1), PoolV1TreeError> {
        let validated = ValidatedIncrementalMerkleTreeV1::from_parts(
            self.next_leaf_index,
            self.root,
            self.frontier,
            empty,
        )?;
        validated
            .append_one(leaf)
            .map(|(next, receipt)| (next.into_inner(), receipt))
    }

    /// Atomically append two ordered leaves.
    ///
    /// Capacity for both leaves is checked before the first transition, so a
    /// one-slot remainder returns `InsufficientCapacity` with no intermediate
    /// state for callers to accidentally persist.
    pub fn append_two(
        &self,
        first_leaf: Digest,
        second_leaf: Digest,
    ) -> Result<(Self, AppendTwoV1), PoolV1TreeError> {
        let empty = pool_v1_empty_roots();
        self.append_two_with_empty_roots(first_leaf, second_leaf, &empty)
    }

    pub fn append_two_with_empty_roots(
        &self,
        first_leaf: Digest,
        second_leaf: Digest,
        empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
    ) -> Result<(Self, AppendTwoV1), PoolV1TreeError> {
        let validated = ValidatedIncrementalMerkleTreeV1::from_parts(
            self.next_leaf_index,
            self.root,
            self.frontier,
            empty,
        )?;
        validated
            .append_two(first_leaf, second_leaf)
            .map(|(next, receipts)| (next.into_inner(), receipts))
    }

    pub fn encode(&self) -> Result<[u8; POOL_V1_TREE_STATE_ACCOUNT_BYTES], PoolV1TreeError> {
        let empty = pool_v1_empty_roots();
        self.encode_with_empty_roots(&empty)
    }

    pub fn encode_with_empty_roots(
        &self,
        empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
    ) -> Result<[u8; POOL_V1_TREE_STATE_ACCOUNT_BYTES], PoolV1TreeError> {
        self.validate_with_empty_roots(empty)?;
        let mut output = [0u8; POOL_V1_TREE_STATE_ACCOUNT_BYTES];
        output[..4].copy_from_slice(&POOL_V1_TREE_STATE_MAGIC);
        output[4] = POOL_V1_TREE_STATE_VERSION;
        output[5] = POOL_V1_TREE_DEPTH as u8;
        output[6] = POOL_V1_TREE_HASH_VERSION;
        output[7] = POOL_V1_DIGEST_ENCODING_VERSION;
        output[8..16].copy_from_slice(&self.next_leaf_index.to_le_bytes());
        output[16..48].copy_from_slice(&encode_digest_canonical(&self.root));
        for (level, node) in self.frontier.iter().enumerate() {
            let start = POOL_V1_TREE_STATE_HEADER_BYTES + level * 32;
            output[start..start + 32].copy_from_slice(&encode_digest_canonical(node));
        }
        Ok(output)
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, PoolV1TreeError> {
        let empty = pool_v1_empty_roots();
        Self::decode_with_empty_roots(bytes, &empty)
    }

    pub fn decode_with_empty_roots(
        bytes: &[u8],
        empty: &[Digest; POOL_V1_TREE_DEPTH + 1],
    ) -> Result<Self, PoolV1TreeError> {
        // Explicit match instead of `Result::map` with the method path as a function
        // value, which the translator rejects. Same value, same error.
        match ValidatedIncrementalMerkleTreeV1::decode(bytes, empty) {
            Ok(validated) => Ok(validated.into_inner()),
            Err(err) => Err(err),
        }
    }
}

#[cfg(test)]
mod x2b_decode_with_empty_roots_differential {
    use super::*;

    /// The frozen body of `IncrementalMerkleTreeV1::decode_with_empty_roots` (commit 3d700effcabe).
    fn frozen(bytes: &[u8], empty: &[Digest; POOL_V1_TREE_DEPTH + 1]) -> Result<IncrementalMerkleTreeV1, PoolV1TreeError> {
        ValidatedIncrementalMerkleTreeV1::decode(bytes, empty).map(ValidatedIncrementalMerkleTreeV1::into_inner)
    }

    fn next(state: &mut u64) -> u64 {
        *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        *state >> 33
    }

    #[test]
    fn same_result_as_frozen_body() {
        let empty = pool_v1_empty_roots();
        let mut state = 0xdec0_de_u64;
        let mut tree = IncrementalMerkleTreeV1::empty();
        for step in 0..40u32 {
            let bytes = tree.encode().unwrap();
            assert_eq!(IncrementalMerkleTreeV1::decode_with_empty_roots(&bytes, &empty), frozen(&bytes, &empty));
            // one-byte mutations at random positions (mostly rejected, some accepted)
            for _ in 0..20 {
                let mut mutated = bytes;
                let at = (next(&mut state) as usize) % mutated.len();
                mutated[at] ^= 1u8 << (next(&mut state) % 8);
                assert_eq!(
                    IncrementalMerkleTreeV1::decode_with_empty_roots(&mutated, &empty),
                    frozen(&mutated, &empty)
                );
            }
            // wrong lengths
            assert_eq!(
                IncrementalMerkleTreeV1::decode_with_empty_roots(&bytes[..bytes.len() - 1], &empty),
                frozen(&bytes[..bytes.len() - 1], &empty)
            );
            assert_eq!(IncrementalMerkleTreeV1::decode_with_empty_roots(&[], &empty), frozen(&[], &empty));
            let leaf = core::array::from_fn(|i| aspis_core::field::M31((step * 31 + i as u32 * 7) % aspis_core::field::P));
            tree = tree.append_one(leaf).unwrap().0;
        }
    }
}

impl Default for IncrementalMerkleTreeV1 {
    fn default() -> Self {
        Self::empty()
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;
    use aspis_core::field::P;

    use super::*;

    fn digest(seed: u32) -> Digest {
        core::array::from_fn(|index| M31((seed + 101 * index as u32) % P))
    }

    fn reference_prefix_root(leaves: &[Digest]) -> Digest {
        let empty = pool_v1_empty_roots();
        if leaves.is_empty() {
            return empty[POOL_V1_TREE_DEPTH];
        }
        let mut level_nodes = leaves.to_vec();
        for level in 0..POOL_V1_TREE_DEPTH {
            if level_nodes.len() & 1 == 1 {
                level_nodes.push(empty[level]);
            }
            let mut parents = Vec::with_capacity(level_nodes.len() / 2);
            for pair in level_nodes.chunks_exact(2) {
                parents.push(pool_v1_tree_parent(&pair[0], &pair[1]));
            }
            level_nodes = parents;
        }
        assert_eq!(level_nodes.len(), 1);
        level_nodes[0]
    }

    fn reference_complete_block_root(leaves: &[Digest]) -> Digest {
        assert!(!leaves.is_empty() && leaves.len().is_power_of_two());
        let mut level_nodes = leaves.to_vec();
        while level_nodes.len() > 1 {
            level_nodes = level_nodes
                .chunks_exact(2)
                .map(|pair| pool_v1_tree_parent(&pair[0], &pair[1]))
                .collect();
        }
        level_nodes[0]
    }

    fn one_slot_remaining_state() -> IncrementalMerkleTreeV1 {
        let empty = pool_v1_empty_roots();
        let frontier = core::array::from_fn(|level| digest(10_000 + level as u32));
        let provisional = IncrementalMerkleTreeV1 {
            next_leaf_index: POOL_V1_LEAF_CAPACITY - 1,
            root: [M31::ZERO; DIGEST_ELEMS],
            frontier,
        };
        let root = provisional.reconstruct_nonfull_root(&empty).unwrap();
        IncrementalMerkleTreeV1::from_parts(provisional.next_leaf_index, root, provisional.frontier)
            .unwrap()
    }

    #[test]
    fn recursive_empty_roots_and_empty_state_are_exact() {
        let roots = pool_v1_empty_roots();
        assert_eq!(roots[0], [M31::ZERO; DIGEST_ELEMS]);
        for level in 0..POOL_V1_TREE_DEPTH {
            assert_eq!(
                roots[level + 1],
                pool_v1_tree_parent(&roots[level], &roots[level])
            );
        }
        let state = IncrementalMerkleTreeV1::empty();
        assert_eq!(state.root, roots[POOL_V1_TREE_DEPTH]);
        assert_eq!(state.frontier, core::array::from_fn(|level| roots[level]));
        assert_eq!(state.validate(), Ok(()));
    }

    #[test]
    fn one_leaf_append_matches_independent_prefix_tree() {
        let mut state = IncrementalMerkleTreeV1::empty();
        let mut leaves = Vec::new();
        assert!(state.append_one(digest(1)).is_ok());
        for index in 0..257u32 {
            let leaf = digest(index + 1);
            let (next, receipt) = state.append_one(leaf).unwrap();
            leaves.push(leaf);
            assert_eq!(receipt.leaf_index, u64::from(index));
            assert_eq!(receipt.root_sequence, u64::from(index) + 1);
            assert_eq!(
                receipt.history,
                root_history_location(receipt.root_sequence)
            );
            assert_eq!(receipt.root, reference_prefix_root(&leaves));
            assert_eq!(next.root, receipt.root);
            let empty = pool_v1_empty_roots();
            let count = leaves.len();
            for level in 0..POOL_V1_TREE_DEPTH {
                if (count >> level) & 1 == 0 {
                    assert_eq!(next.frontier[level], empty[level]);
                } else {
                    let block_len = 1usize << level;
                    let block_end = count - (count & (block_len - 1));
                    let block_start = block_end - block_len;
                    assert_eq!(
                        next.frontier[level],
                        reference_complete_block_root(&leaves[block_start..block_end])
                    );
                }
            }
            state = next;
        }
    }

    #[test]
    fn two_leaf_append_is_exactly_two_ordered_appends() {
        let state = IncrementalMerkleTreeV1::empty();
        let a = digest(1);
        let b = digest(2);
        let (two_state, two) = state.append_two(a, b).unwrap();
        let (one_state, first) = state.append_one(a).unwrap();
        let (sequential_state, second) = one_state.append_one(b).unwrap();
        assert_eq!(two_state, sequential_state);
        assert_eq!(two, AppendTwoV1 { first, second });
        assert_eq!(two.first.leaf_index, 0);
        assert_eq!(two.second.leaf_index, 1);
    }

    #[test]
    fn sealed_validated_tree_matches_plain_api_and_rejects_corrupt_sources() {
        let empty = pool_v1_empty_roots();
        let plain = IncrementalMerkleTreeV1::empty();
        let sealed = ValidatedIncrementalMerkleTreeV1::from_parts(
            plain.next_leaf_index,
            plain.root,
            plain.frontier,
            &empty,
        )
        .unwrap();

        let (sealed_one, sealed_one_receipt) = sealed.append_one(digest(81)).unwrap();
        let (plain_one, plain_one_receipt) = plain
            .append_one_with_empty_roots(digest(81), &empty)
            .unwrap();
        assert_eq!(sealed_one.into_inner(), plain_one);
        assert_eq!(sealed_one_receipt, plain_one_receipt);

        let sealed_one = ValidatedIncrementalMerkleTreeV1::from_parts(
            plain_one.next_leaf_index,
            plain_one.root,
            plain_one.frontier,
            &empty,
        )
        .unwrap();
        let (sealed_two, sealed_two_receipts) =
            sealed_one.append_two(digest(82), digest(83)).unwrap();
        let (plain_two, plain_two_receipts) = plain_one
            .append_two_with_empty_roots(digest(82), digest(83), &empty)
            .unwrap();
        assert_eq!(sealed_two.into_inner(), plain_two);
        assert_eq!(sealed_two_receipts, plain_two_receipts);
        assert_eq!(plain_two.validate_with_empty_roots(&empty), Ok(()));

        let encoded = plain_two.encode_with_empty_roots(&empty).unwrap();
        assert_eq!(
            ValidatedIncrementalMerkleTreeV1::decode(&encoded, &empty)
                .unwrap()
                .into_inner(),
            plain_two
        );

        let mut corrupt_root = plain_two;
        corrupt_root.root = digest(99_001);
        assert_eq!(
            ValidatedIncrementalMerkleTreeV1::from_parts(
                corrupt_root.next_leaf_index,
                corrupt_root.root,
                corrupt_root.frontier,
                &empty,
            ),
            Err(PoolV1TreeError::RootMismatch)
        );
        let mut wrong_empty = empty;
        wrong_empty[0] = digest(99_002);
        assert!(ValidatedIncrementalMerkleTreeV1::from_parts(
            plain.next_leaf_index,
            plain.root,
            plain.frontier,
            &wrong_empty,
        )
        .is_err());
    }

    #[test]
    fn terminal_state_is_created_by_final_append_and_checked_by_history() {
        let state = one_slot_remaining_state();
        let before = state;
        assert_eq!(
            state.append_two(digest(1), digest(2)),
            Err(PoolV1TreeError::InsufficientCapacity)
        );
        assert_eq!(state, before);

        let (full, receipt) = state.append_one(digest(3)).unwrap();
        assert_eq!(receipt.leaf_index, POOL_V1_LEAF_CAPACITY - 1);
        assert_eq!(receipt.root_sequence, POOL_V1_LEAF_CAPACITY);
        assert_eq!(
            receipt.history,
            root_history_location(POOL_V1_LEAF_CAPACITY)
        );
        assert_eq!(full.next_leaf_index, POOL_V1_LEAF_CAPACITY);
        assert_eq!(
            full.frontier,
            core::array::from_fn(|level| pool_v1_empty_roots()[level])
        );
        assert_eq!(full.validate(), Ok(()));
        assert_eq!(
            full.validate_terminal_root_against_history(&receipt.root),
            Ok(())
        );
        assert_eq!(
            full.validate_terminal_root_against_history(&digest(99_999)),
            Err(PoolV1TreeError::RootMismatch)
        );
        assert_eq!(full.append_one(digest(4)), Err(PoolV1TreeError::TreeFull));
    }

    #[test]
    fn corrupt_root_and_inactive_frontier_fail_closed() {
        let empty = IncrementalMerkleTreeV1::empty();
        let mut corrupt_root = empty;
        corrupt_root.root = digest(999);
        assert_eq!(corrupt_root.validate(), Err(PoolV1TreeError::RootMismatch));
        assert_eq!(
            corrupt_root.append_one(digest(1)),
            Err(PoolV1TreeError::RootMismatch)
        );

        let mut corrupt_frontier = empty;
        corrupt_frontier.frontier[0] = digest(998);
        assert_eq!(
            corrupt_frontier.validate(),
            Err(PoolV1TreeError::NonCanonicalFrontier)
        );
    }

    #[test]
    fn tree_state_account_image_roundtrips_and_rejects_bad_versions() {
        let (state, _) = IncrementalMerkleTreeV1::empty()
            .append_two(digest(1), digest(2))
            .unwrap();
        let encoded = state.encode().unwrap();
        assert_eq!(encoded.len(), 688);
        assert_eq!(IncrementalMerkleTreeV1::decode(&encoded), Ok(state));

        let mut bad_hash = encoded;
        bad_hash[6] += 1;
        assert_eq!(
            IncrementalMerkleTreeV1::decode(&bad_hash),
            Err(PoolV1TreeError::WrongTreeHash)
        );

        let mut noncanonical = encoded;
        noncanonical[16..20].copy_from_slice(&P.to_le_bytes());
        assert_eq!(
            IncrementalMerkleTreeV1::decode(&noncanonical),
            Err(PoolV1TreeError::NonCanonicalDigest)
        );
    }
}

// Proof/extraction-only owned reference; excluded from all shipped builds.
#[cfg(any(kani, aeneas_ref))]
#[path = "../../../../tools/r1-builder-reference/tree.rs"]
pub mod tree_reference;

/// `decode_tree_image_unvalidated` against its frozen frontier loop (commit 3d700effcabe), kept here; and the
/// nullifier marker's digest check against `iter().all`.
#[cfg(test)]
mod x2c_tree_image_differential {
    use super::*;

    fn frozen(bytes: &[u8]) -> Result<IncrementalMerkleTreeV1, PoolV1TreeError> {
        if bytes.len() != POOL_V1_TREE_STATE_ACCOUNT_BYTES {
            return Err(PoolV1TreeError::WrongLength);
        }
        if bytes[..4] != POOL_V1_TREE_STATE_MAGIC {
            return Err(PoolV1TreeError::WrongMagic);
        }
        if bytes[4] != POOL_V1_TREE_STATE_VERSION {
            return Err(PoolV1TreeError::WrongVersion);
        }
        if bytes[5] != POOL_V1_TREE_DEPTH as u8 {
            return Err(PoolV1TreeError::WrongDepth);
        }
        if bytes[6] != POOL_V1_TREE_HASH_VERSION {
            return Err(PoolV1TreeError::WrongTreeHash);
        }
        if bytes[7] != POOL_V1_DIGEST_ENCODING_VERSION {
            return Err(PoolV1TreeError::WrongDigestEncoding);
        }
        let next_leaf_index = u64::from_le_bytes(bytes[8..16].try_into().unwrap());
        let root = decode_digest_canonical(bytes[16..48].try_into().unwrap())
            .map_err(|_| PoolV1TreeError::NonCanonicalDigest)?;
        let mut frontier = [[M31::ZERO; DIGEST_ELEMS]; POOL_V1_TREE_DEPTH];
        for (level, node) in frontier.iter_mut().enumerate() {
            let start = POOL_V1_TREE_STATE_HEADER_BYTES + level * 32;
            *node = decode_digest_canonical(bytes[start..start + 32].try_into().unwrap())
                .map_err(|_| PoolV1TreeError::NonCanonicalDigest)?;
        }
        Ok(IncrementalMerkleTreeV1 { next_leaf_index, root, frontier })
    }

    #[test]
    fn x2c_same_result_as_frozen_body() {
        let mut seed = 77u64;
        let mut next = || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            seed >> 33
        };
        for round in 0..4_000u64 {
            let mut bytes = alloc::vec![0u8; POOL_V1_TREE_STATE_ACCOUNT_BYTES];
            bytes[..4].copy_from_slice(&POOL_V1_TREE_STATE_MAGIC);
            bytes[4] = POOL_V1_TREE_STATE_VERSION;
            bytes[5] = POOL_V1_TREE_DEPTH as u8;
            bytes[6] = POOL_V1_TREE_HASH_VERSION;
            bytes[7] = POOL_V1_DIGEST_ENCODING_VERSION;
            let mut at = 8;
            while at + 4 <= bytes.len() {
                let v = (next() as u32) % aspis_core::field::P;
                bytes[at..at + 4].copy_from_slice(&v.to_le_bytes());
                at += 4;
            }
            match round % 4 {
                0 => {}
                1 => {
                    let level = (next() as usize) % POOL_V1_TREE_DEPTH;
                    let at = POOL_V1_TREE_STATE_HEADER_BYTES + level * 32 + 4 * ((next() as usize) % 8);
                    bytes[at..at + 4].copy_from_slice(&aspis_core::field::P.to_le_bytes());
                }
                2 => {
                    let at = (next() as usize) % 8;
                    bytes[at] ^= 1;
                }
                _ => {
                    bytes.pop();
                }
            }
            assert_eq!(decode_tree_image_unvalidated(&bytes), frozen(&bytes));
        }
    }
}

/// `append_one` and `validate_with_empty_roots` against their frozen bodies (commit 3d700effcabe), kept here.
#[cfg(test)]
mod x2c_append_validate_differential {
    use super::*;

    fn frozen_validate(t: &IncrementalMerkleTreeV1, empty: &[Digest; POOL_V1_TREE_DEPTH + 1]) -> Result<(), PoolV1TreeError> {
        if t.next_leaf_index > POOL_V1_LEAF_CAPACITY {
            return Err(PoolV1TreeError::IndexOutOfRange);
        }
        for level in 0..POOL_V1_TREE_DEPTH {
            if (t.next_leaf_index >> level) & 1 == 0 && t.frontier[level] != empty[level] {
                return Err(PoolV1TreeError::NonCanonicalFrontier);
            }
        }
        if t.next_leaf_index == 0 {
            return if t.root == empty[POOL_V1_TREE_DEPTH] { Ok(()) } else { Err(PoolV1TreeError::RootMismatch) };
        }
        if t.next_leaf_index < POOL_V1_LEAF_CAPACITY && t.reconstruct_nonfull_root(empty)? != t.root {
            return Err(PoolV1TreeError::RootMismatch);
        }
        Ok(())
    }

    fn frozen_append(t: &IncrementalMerkleTreeV1, leaf: Digest, empty: &[Digest; POOL_V1_TREE_DEPTH + 1]) -> Result<(IncrementalMerkleTreeV1, AppendOneV1), PoolV1TreeError> {
        if t.next_leaf_index == POOL_V1_LEAF_CAPACITY {
            return Err(PoolV1TreeError::TreeFull);
        }
        let leaf_index = t.next_leaf_index;
        let mut frontier = t.frontier;
        let mut carry = leaf;
        let mut carry_level = 0usize;
        while carry_level < POOL_V1_TREE_DEPTH && (leaf_index >> carry_level) & 1 == 1 {
            carry = pool_v1_tree_parent(&frontier[carry_level], &carry);
            frontier[carry_level] = empty[carry_level];
            carry_level += 1;
        }
        let next_leaf_index = leaf_index + 1;
        let root = if carry_level == POOL_V1_TREE_DEPTH {
            carry
        } else {
            frontier[carry_level] = carry;
            let provisional = IncrementalMerkleTreeV1 { next_leaf_index, root: [M31::ZERO; DIGEST_ELEMS], frontier };
            provisional.reconstruct_nonfull_root_from_level(empty, carry_level)?
        };
        Ok((
            IncrementalMerkleTreeV1 { next_leaf_index, root, frontier },
            AppendOneV1 { leaf_index, root_sequence: next_leaf_index, root, history: root_history_location(next_leaf_index) },
        ))
    }

    #[test]
    fn x2c_append_and_validate_match_frozen() {
        let empty = pool_v1_empty_roots();
        let mut seed = 99u64;
        let mut next = move || {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            seed >> 33
        };
        // A valid chain of appends from empty, checked at every step, plus mutated copies.
        let mut tree = IncrementalMerkleTreeV1 { next_leaf_index: 0, root: empty[POOL_V1_TREE_DEPTH], frontier: core::array::from_fn(|l| empty[l]) };
        for step in 0..200u64 {
            let leaf: Digest = core::array::from_fn(|_| M31((next() as u32) % aspis_core::field::P));
            assert_eq!(tree.validate_with_empty_roots(&empty), frozen_validate(&tree, &empty));
            let mut bad = tree;
            match step % 3 {
                0 => bad.root[0] = M31((bad.root[0].0 + 1) % aspis_core::field::P),
                1 => bad.frontier[(next() as usize) % POOL_V1_TREE_DEPTH][1] = M31(7),
                _ => bad.next_leaf_index = POOL_V1_LEAF_CAPACITY + (next() % 3),
            }
            assert_eq!(bad.validate_with_empty_roots(&empty), frozen_validate(&bad, &empty));
            let validated = ValidatedIncrementalMerkleTreeV1::from_parts(tree.next_leaf_index, tree.root, tree.frontier, &empty).unwrap();
            let (next_tree, receipt) = validated.append_one(leaf).unwrap();
            let (frozen_tree, frozen_receipt) = frozen_append(&tree, leaf, &empty).unwrap();
            assert_eq!(next_tree.into_inner(), frozen_tree);
            assert_eq!(receipt, frozen_receipt);
            tree = frozen_tree;
        }
        // Near capacity and at capacity (core over plain values, frontier as found).
        for index in [POOL_V1_LEAF_CAPACITY - 2, POOL_V1_LEAF_CAPACITY - 1, POOL_V1_LEAF_CAPACITY] {
            let t = IncrementalMerkleTreeV1 { next_leaf_index: index, root: tree.root, frontier: tree.frontier };
            let leaf: Digest = core::array::from_fn(|_| M31((next() as u32) % aspis_core::field::P));
            assert_eq!(append_one_core_v1(t.next_leaf_index, t.frontier, leaf, &empty), frozen_append(&t, leaf, &empty));
        }
    }
}
