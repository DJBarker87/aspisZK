//! ADOPTED R1 PROOF FORMAT (PREREG-PROOF-SIZE-2, 2026-10-19); UNPROVED.
//!
//! Indexed Merkle multiproofs over the fixed 2^18-leaf commitment domain.
//! `Arity::Eight` is the shipped tree shape (six levels of eight, node grammar
//! `0x18 || c0..c7`); `Arity::Two` is the candidate binary tree (eighteen
//! levels, node grammar `BINARY_NODE_TAG || left || right`). Leaf hashing is
//! unchanged and supplied by the caller.
//!
//! Multiproof order: level by level from the leaves; inside a level, occupied
//! nodes in ascending index order; inside one parent's group, the children
//! that are not occupied, in ascending slot order. The number of supplied
//! nodes is a function of the index set only (`node_count`), so a parser
//! knows the exact length before reading a node.
use alloc::vec::Vec;
use aspis_core::{r0::merkle, Digest32};

/// Leaves in every committed tree (C1, C2 and the padded folded tree).
pub const LEAF_BITS: u32 = 18;
/// New domain separator for binary parent nodes (leaves use 0x10, eight-way
/// parents 0x18). UNPROVED: its disjointness is one of the obligations.
pub const BINARY_NODE_TAG: u8 = 0x12;
/// Largest index set one multiproof call accepts (one transaction batch).
pub const MAX_BATCH: usize = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arity {
    Two,
    Eight,
}
impl Arity {
    #[inline(always)]
    pub const fn bits(self) -> u32 {
        match self {
            Self::Two => 1,
            Self::Eight => 3,
        }
    }
    #[inline(always)]
    pub const fn width(self) -> usize {
        1 << self.bits()
    }
    #[inline(always)]
    pub const fn levels(self) -> u32 {
        LEAF_BITS / self.bits()
    }
}

#[inline(always)]
pub fn binary_parent<H: Digest32>(hash: H, left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    hash.digest(&[&[BINARY_NODE_TAG], left, right])
}

/// Strictly increasing and inside the leaf domain.
fn well_formed(indices: &[u32]) -> bool {
    !indices.is_empty()
        && indices.len() <= MAX_BATCH
        && indices.windows(2).all(|w| w[0] < w[1])
        && indices.iter().all(|&i| i < 1 << LEAF_BITS)
}

#[inline(always)]
fn index_at(indices: &[u32; MAX_BATCH], index: usize) -> u32 {
    indices[index]
}

#[inline(always)]
fn value_at(values: &[[u8; 32]; MAX_BATCH], index: usize) -> [u8; 32] { values[index] }

#[inline(always)]
fn root_matches(values: &[[u8; 32]; MAX_BATCH], root: &[u8; 32]) -> bool { values[0] == *root }

#[inline(always)]
fn occupied_binary_parent<H: Digest32>(hash: H, values: &[[u8; 32]; MAX_BATCH], index: usize) -> [u8; 32] {
    hash.digest(&[&[BINARY_NODE_TAG], &values[index], &values[index + 1]])
}

#[inline(always)]
fn sibling_binary_parent<H: Digest32>(hash: H, values: &[[u8; 32]; MAX_BATCH], index: usize, sibling: &[u8], left: bool) -> [u8; 32] {
    if left { hash.digest(&[&[BINARY_NODE_TAG], &values[index], sibling]) }
    else { hash.digest(&[&[BINARY_NODE_TAG], sibling, &values[index]]) }
}

/// Number of supplied sibling nodes for a strictly increasing index set:
/// at each level, (width x distinct parents) - occupied nodes.
pub fn node_count(arity: Arity, indices: &[u32]) -> Option<usize> {
    if !well_formed(indices) {
        return None;
    }
    let mut level = [0u32; MAX_BATCH];
    level[..indices.len()].copy_from_slice(indices);
    let mut n = indices.len();
    let mut count = 0;
    for _ in 0..arity.levels() {
        let mut w = 0;
        let mut i = 0;
        while i < n {
            let parent = index_at(&level, i) >> arity.bits();
            let mut j = i;
            while j < n && index_at(&level, j) >> arity.bits() == parent {
                j += 1;
            }
            count += arity.width() - (j - i);
            level[w] = parent;
            w += 1;
            i = j;
        }
        n = w;
    }
    Some(count)
}

/// Verify one multiproof. `indices` strictly increasing, `leaves[i]` the leaf
/// hash at `indices[i]`, `nodes` exactly `32 * node_count` bytes, consumed in
/// the canonical order. Rejects on any malformed input; never panics.
pub fn verify<H: Digest32>(
    hash: H,
    arity: Arity,
    root: &[u8; 32],
    indices: &[u32],
    leaves: &[[u8; 32]],
    nodes: &[u8],
) -> bool {
    if !well_formed(indices) || leaves.len() != indices.len() || nodes.len() % 32 != 0 {
        return false;
    }
    let mut idx = [0u32; MAX_BATCH];
    let mut val = [[0u8; 32]; MAX_BATCH];
    let n = indices.len();
    idx[..n].copy_from_slice(indices);
    val[..n].copy_from_slice(leaves);
    verify_in_place(hash, arity, root, &mut idx, &mut val, n, nodes)
}

/// `verify` over caller-owned scratch arrays (no copies): the first `n`
/// entries of `idx`/`val` are the strictly increasing indices and their
/// leaves; both arrays are overwritten.
#[inline(always)]
pub fn verify_in_place<H: Digest32>(
    hash: H,
    arity: Arity,
    root: &[u8; 32],
    idx: &mut [u32; MAX_BATCH],
    val: &mut [[u8; 32]; MAX_BATCH],
    mut n: usize,
    nodes: &[u8],
) -> bool {
    if n == 0 || n > MAX_BATCH || !well_formed(&idx[..n]) || nodes.len() % 32 != 0 {
        return false;
    }
    let mut at = 0usize;
    for _ in 0..arity.levels() {
        let mut w = 0;
        let mut i = 0;
        while i < n {
            let parent = index_at(idx, i) >> arity.bits();
            let digest = match arity {
                Arity::Two => {
                    // Hash straight from the stored slices: no sibling or
                    // pair copies (SBF cost; same grammar and order).
                    if i + 1 < n && index_at(idx, i + 1) == index_at(idx, i) ^ 1 {
                        let d = occupied_binary_parent(hash, val, i);
                        i += 2;
                        d
                    } else {
                        let Some(sibling) = nodes.get(at..at + 32) else { return false };
                        at += 32;
                        let d = sibling_binary_parent(hash, val, i, sibling, index_at(idx, i) & 1 == 0);
                        i += 1;
                        d
                    }
                }
                Arity::Eight => {
                    let mut children = [[0u8; 32]; 8];
                    for (slot, child) in children.iter_mut().enumerate() {
                        if i < n && index_at(idx, i) >> 3 == parent && (index_at(idx, i) & 7) as usize == slot {
                            *child = value_at(val, i);
                            i += 1;
                        } else {
                            let Some(sibling) = nodes.get(at..at + 32) else { return false };
                            child.copy_from_slice(sibling);
                            at += 32;
                        }
                    }
                    merkle::parent_with_digest(hash, &children)
                }
            };
            idx[w] = parent;
            val[w] = digest;
            w += 1;
        }
        n = w;
    }
    n == 1 && index_at(idx, 0) == 0 && root_matches(val, root) && at == nodes.len()
}

/// FUTURE-VERSION EXPERIMENT E4a: outcome of `verify_counting`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Counted {
    /// The index set is not well formed (what `node_count` reports as `None`).
    Malformed,
    /// The traversal needs more sibling nodes than the slot holds (what the
    /// two-pass form sees as `node_count > slot nodes`).
    Short,
    /// Traversal complete: whether the recomputed root matches, and the bytes
    /// of the slot consumed (`32 * node_count`).
    Done { root_ok: bool, used: usize },
}

/// FUTURE-VERSION EXPERIMENT E4a (binary trees only): `verify_in_place` over a
/// whole fixed slot, counting the sibling nodes it consumes instead of taking
/// a pre-counted prefix. Same hash inputs in the same order as
/// `verify_in_place` on the first `node_count` nodes; the number consumed
/// equals `node_count` because both are functions of the index set alone.
#[inline(always)]
pub fn verify_counting<H: Digest32>(
    hash: H,
    root: &[u8; 32],
    idx: &mut [u32; MAX_BATCH],
    val: &mut [[u8; 32]; MAX_BATCH],
    mut n: usize,
    slot: &[u8],
) -> Counted {
    if n == 0 || n > MAX_BATCH || !well_formed(&idx[..n]) {
        return Counted::Malformed;
    }
    let mut at = 0usize;
    for _ in 0..Arity::Two.levels() {
        let mut w = 0;
        let mut i = 0;
        while i < n {
            let parent = index_at(idx, i) >> 1;
            let digest = if i + 1 < n && index_at(idx, i + 1) == index_at(idx, i) ^ 1 {
                let d = occupied_binary_parent(hash, val, i);
                i += 2;
                d
            } else {
                let Some(sibling) = slot.get(at..at + 32) else { return Counted::Short };
                at += 32;
                let d = sibling_binary_parent(hash, val, i, sibling, index_at(idx, i) & 1 == 0);
                i += 1;
                d
            };
            idx[w] = parent;
            val[w] = digest;
            w += 1;
        }
        n = w;
    }
    Counted::Done { root_ok: n == 1 && index_at(idx, 0) == 0 && root_matches(val, root), used: at }
}

/// FUTURE-VERSION EXPERIMENT E4b: `verify_counting` with each parent digest
/// written straight into the next level's buffer. Two buffers alternate, so an
/// output never overlaps its inputs. Same hash inputs in the same order.
#[inline(always)]
pub fn verify_counting_direct<H: Digest32>(
    hash: H,
    root: &[u8; 32],
    idx: &mut [u32; MAX_BATCH],
    val: &mut [[u8; 32]; MAX_BATCH],
    mut n: usize,
    slot: &[u8],
) -> Counted {
    if n == 0 || n > MAX_BATCH || !well_formed(&idx[..n]) {
        return Counted::Malformed;
    }
    let mut other = [[0u8; 32]; MAX_BATCH];
    let (mut cur, mut nxt): (&mut [[u8; 32]; MAX_BATCH], &mut [[u8; 32]; MAX_BATCH]) = (val, &mut other);
    let tag = [BINARY_NODE_TAG];
    let mut at = 0usize;
    for _ in 0..Arity::Two.levels() {
        let mut w = 0;
        let mut i = 0;
        while i < n {
            let index = idx[i];
            if i + 1 < n && idx[i + 1] == index ^ 1 {
                hash.digest_into(&[&tag, &cur[i], &cur[i + 1]], &mut nxt[w]);
                i += 2;
            } else {
                let Some(sibling) = slot.get(at..at + 32) else { return Counted::Short };
                at += 32;
                if index & 1 == 0 {
                    hash.digest_into(&[&tag, &cur[i], sibling], &mut nxt[w]);
                } else {
                    hash.digest_into(&[&tag, sibling, &cur[i]], &mut nxt[w]);
                }
                i += 1;
            }
            idx[w] = index >> 1;
            w += 1;
        }
        n = w;
        core::mem::swap(&mut cur, &mut nxt);
    }
    Counted::Done { root_ok: n == 1 && idx[0] == 0 && cur[0] == *root, used: at }
}

/// Aspis proof format: largest index set of one merged
/// multiproof, all 22 queries of a tree.
pub const MAX_MERGED: usize = 22;

/// Strictly increasing, inside the leaf domain, at most `MAX_MERGED` entries.
fn well_formed_merged(indices: &[u32]) -> bool {
    if indices.is_empty() || indices.len() > MAX_MERGED {
        return false;
    }
    let mut ok = indices[0] < 1 << LEAF_BITS;
    let mut i = 1;
    while i < indices.len() {
        ok = ok && indices[i - 1] < indices[i] && indices[i] < 1 << LEAF_BITS;
        i += 1;
    }
    ok
}

/// `node_count` for a binary tree and an index set of up to `MAX_MERGED`
/// entries: the number of supplied sibling nodes, a function of the index set
/// alone.
pub fn node_count_merged(indices: &[u32]) -> Option<usize> {
    if !well_formed_merged(indices) {
        return None;
    }
    let mut level = [0u32; MAX_MERGED];
    level[..indices.len()].copy_from_slice(indices);
    let mut n = indices.len();
    let mut count = 0;
    for _ in 0..Arity::Two.levels() {
        let mut w = 0;
        let mut i = 0;
        while i < n {
            if i + 1 < n && level[i + 1] == level[i] ^ 1 {
                level[w] = level[i] >> 1;
                i += 2;
            } else {
                count += 1;
                level[w] = level[i] >> 1;
                i += 1;
            }
            w += 1;
        }
        n = w;
    }
    Some(count)
}

/// `verify_counting_direct` for an index set of up to `MAX_MERGED` entries.
/// Same node grammar, same canonical order, same verdict type.
#[inline(always)]
pub fn verify_counting_merged<H: Digest32>(
    hash: H,
    root: &[u8; 32],
    idx: &mut [u32; MAX_MERGED],
    val: &mut [[u8; 32]; MAX_MERGED],
    mut n: usize,
    slot: &[u8],
) -> Counted {
    if n == 0 || n > MAX_MERGED || !well_formed_merged(&idx[..n]) {
        return Counted::Malformed;
    }
    // Eighteen levels as nine pairs: `val` to `other`, then `other` back to `val`. The same digests in the
    // same order as exchanging two buffer references each level; the result is in `val`.
    let mut other = [[0u8; 32]; MAX_MERGED];
    let mut at = 0usize;
    let mut short = false;
    let mut pair = 0;
    while pair < 9 && !short {
        match merged_level(hash, idx, val, &mut other, n, slot, at) {
            None => short = true,
            Some((w, a)) => match merged_level(hash, idx, &other, val, w, slot, a) {
                None => short = true,
                Some((w2, a2)) => {
                    n = w2;
                    at = a2;
                }
            },
        }
        pair += 1;
    }
    if short {
        return Counted::Short;
    }
    Counted::Done { root_ok: n == 1 && idx[0] == 0 && val[0] == *root, used: at }
}

/// One level of the merged traversal, from `cur` into `nxt`: the new entry count and slot offset, or `None`
/// when the slot holds too few sibling nodes.
#[inline(always)]
fn merged_level<H: Digest32>(
    hash: H,
    idx: &mut [u32; MAX_MERGED],
    cur: &[[u8; 32]; MAX_MERGED],
    nxt: &mut [[u8; 32]; MAX_MERGED],
    n: usize,
    slot: &[u8],
    mut at: usize,
) -> Option<(usize, usize)> {
    // The entry's index is carried from the previous step (read once per entry); same tests, same
    // digests in the same order, same slot reads.
    let tag = [BINARY_NODE_TAG];
    let mut w = 0;
    let mut i = 0;
    let mut index = if n > 0 { idx[0] } else { 0 };
    while i < n {
        let has_next = i + 1 < n;
        let next = if has_next { idx[i + 1] } else { 0 };
        let parent = index >> 1u32;
        if has_next && next == index ^ 1 {
            hash.digest_into(&[&tag, &cur[i], &cur[i + 1]], &mut nxt[w]);
            i += 2;
            index = if i < n { idx[i] } else { 0 };
        } else {
            let Some(sibling) = slot.get(at..at + 32) else { return None };
            at += 32;
            if index & 1 == 0 {
                hash.digest_into(&[&tag, &cur[i], sibling], &mut nxt[w]);
            } else {
                hash.digest_into(&[&tag, sibling, &cur[i]], &mut nxt[w]);
            }
            i += 1;
            index = next;
        }
        idx[w] = parent;
        w += 1;
    }
    Some((w, at))
}

/// Prover side: emit the canonical node sequence. `node(level, index)` returns
/// the stored digest of node `index` at `level` (0 = leaves).
pub fn generate(
    arity: Arity,
    indices: &[u32],
    mut node: impl FnMut(u32, u32) -> [u8; 32],
) -> Option<Vec<u8>> {
    let count = node_count(arity, indices)?;
    let mut out = Vec::with_capacity(32 * count);
    let mut level: Vec<u32> = indices.to_vec();
    for depth in 0..arity.levels() {
        let mut next = Vec::new();
        let mut i = 0;
        while i < level.len() {
            let parent = level[i] >> arity.bits();
            for slot in 0..arity.width() as u32 {
                let child = (parent << arity.bits()) | slot;
                if i < level.len() && level[i] == child {
                    i += 1;
                } else {
                    out.extend_from_slice(&node(depth, child));
                }
            }
            next.push(parent);
        }
        level = next;
    }
    (out.len() == 32 * count).then_some(out)
}

/// Host-side complete binary tree over 2^18 leaves.
#[cfg(feature = "prover")]
pub struct BinaryTree {
    levels: Vec<Vec<[u8; 32]>>,
}
#[cfg(feature = "prover")]
impl BinaryTree {
    pub fn new<H: Digest32>(hash: H, leaves: Vec<[u8; 32]>) -> Option<Self> {
        if leaves.len() != 1 << LEAF_BITS {
            return None;
        }
        let mut levels = Vec::with_capacity(LEAF_BITS as usize + 1);
        levels.push(leaves);
        for depth in 0..LEAF_BITS as usize {
            let next = levels[depth].chunks_exact(2).map(|c| binary_parent(hash, &c[0], &c[1])).collect();
            levels.push(next);
        }
        Some(Self { levels })
    }
    pub fn root(&self) -> [u8; 32] {
        self.levels[LEAF_BITS as usize][0]
    }
    pub fn node(&self, level: u32, index: u32) -> [u8; 32] {
        self.levels[level as usize][index as usize]
    }
    pub fn multiproof(&self, indices: &[u32]) -> Option<Vec<u8>> {
        generate(Arity::Two, indices, |l, i| self.node(l, i))
    }
}

/// Sort a batch of (index, leaf) pairs, merge equal indices whose leaves are
/// identical (the folded tree's shared openings), reject equal indices with
/// different leaves. Returns the number of distinct entries.
pub fn sort_dedup(idx: &mut [u32], val: &mut [[u8; 32]]) -> Option<usize> {
    let n = idx.len();
    if n != val.len() || n == 0 || n > MAX_BATCH {
        return None;
    }
    // Insertion sort: n <= 16.
    for i in 1..n {
        let mut j = i;
        while j > 0 && idx[j - 1] > idx[j] {
            idx.swap(j - 1, j);
            val.swap(j - 1, j);
            j -= 1;
        }
    }
    let mut w = 1;
    for i in 1..n {
        if idx[i] == idx[w - 1] {
            if val[i] != val[w - 1] {
                return None;
            }
        } else {
            idx[w] = idx[i];
            val[w] = val[i];
            w += 1;
        }
    }
    Some(w)
}

#[cfg(all(test, feature = "prover"))]
mod tests {
    use super::*;
    use aspis_core::digest::LegacyHashFn;
    fn h(parts: &[&[u8]]) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        let mut s = Sha256::new();
        for p in parts {
            s.update(p);
        }
        s.finalize().into()
    }
    fn tree() -> BinaryTree {
        let leaves = (0..1u32 << LEAF_BITS).map(|i| h(&[b"leaf", &i.to_le_bytes()])).collect();
        BinaryTree::new(LegacyHashFn(h), leaves).unwrap()
    }
    fn leaves(ix: &[u32]) -> Vec<[u8; 32]> {
        ix.iter().map(|i| h(&[b"leaf", &i.to_le_bytes()])).collect()
    }
    #[test]
    fn binary_roundtrip_and_teeth() {
        let t = tree();
        let hash = LegacyHashFn(h);
        let mut ix: Vec<u32> = (0..12u32).map(|j| j.reverse_bits() >> (32 - LEAF_BITS)).collect();
        ix.sort();
        let lv = leaves(&ix);
        let nodes = t.multiproof(&ix).unwrap();
        assert_eq!(nodes.len(), 32 * 172);
        assert!(verify(hash, Arity::Two, &t.root(), &ix, &lv, &nodes));
        // wrong sibling
        let mut bad = nodes.clone();
        bad[100] ^= 1;
        assert!(!verify(hash, Arity::Two, &t.root(), &ix, &lv, &bad));
        // missing / extra node
        assert!(!verify(hash, Arity::Two, &t.root(), &ix, &lv, &nodes[..nodes.len() - 32]));
        let mut extra = nodes.clone();
        extra.extend_from_slice(&[0; 32]);
        assert!(!verify(hash, Arity::Two, &t.root(), &ix, &lv, &extra));
        // duplicated / misordered index
        let mut dup = ix.clone();
        dup[1] = dup[0];
        assert!(!verify(hash, Arity::Two, &t.root(), &dup, &lv, &nodes));
        let mut mis = ix.clone();
        mis.swap(0, 1);
        assert!(!verify(hash, Arity::Two, &t.root(), &mis, &lv, &nodes));
        // adjacent pair and single leaf
        for set in [&[6u32, 7][..], &[0], &[(1 << LEAF_BITS) - 1], &[1, 2, 3, 4, 5]] {
            let n = t.multiproof(set).unwrap();
            assert_eq!(n.len(), 32 * node_count(Arity::Two, set).unwrap());
            assert!(verify(hash, Arity::Two, &t.root(), set, &leaves(set), &n));
        }
    }
    /// The merged traversal before the carried-index form (as in the X1 source), for comparison.
    fn reference_counting_merged(root: &[u8; 32], idx: &mut [u32; MAX_MERGED], val: &mut [[u8; 32]; MAX_MERGED], mut n: usize, slot: &[u8]) -> Counted {
        let hash = LegacyHashFn(h);
        if n == 0 || n > MAX_MERGED || !well_formed_merged(&idx[..n]) {
            return Counted::Malformed;
        }
        let mut at = 0usize;
        for _ in 0..LEAF_BITS {
            let mut next = [[0u8; 32]; MAX_MERGED];
            let mut w = 0;
            let mut i = 0;
            while i < n {
                let index = idx[i];
                if i + 1 < n && idx[i + 1] == index ^ 1 {
                    next[w] = hash.digest(&[&[BINARY_NODE_TAG], &val[i], &val[i + 1]]);
                    i += 2;
                } else {
                    let Some(sibling) = slot.get(at..at + 32) else { return Counted::Short };
                    at += 32;
                    next[w] = if index & 1 == 0 { hash.digest(&[&[BINARY_NODE_TAG], &val[i], sibling]) } else { hash.digest(&[&[BINARY_NODE_TAG], sibling, &val[i]]) };
                    i += 1;
                }
                idx[w] = index >> 1;
                w += 1;
            }
            val[..w].copy_from_slice(&next[..w]);
            n = w;
        }
        Counted::Done { root_ok: n == 1 && idx[0] == 0 && val[0] == *root, used: at }
    }

    /// The canonical node stream of a binary multiproof over up to `MAX_MERGED` indices.
    fn merged_nodes(t: &BinaryTree, indices: &[u32]) -> Vec<u8> {
        let mut out = Vec::new();
        let mut level: Vec<u32> = indices.to_vec();
        for depth in 0..LEAF_BITS {
            let mut next = Vec::new();
            let mut i = 0;
            while i < level.len() {
                let parent = level[i] >> 1;
                for slot in 0..2u32 {
                    let child = (parent << 1) | slot;
                    if i < level.len() && level[i] == child {
                        i += 1;
                    } else {
                        out.extend_from_slice(&t.node(depth, child));
                    }
                }
                next.push(parent);
            }
            level = next;
        }
        out
    }

    /// `verify_counting_merged` gives the reference verdict on random index sets of 1 to 22
    /// leaves (adjacent pairs included), with the honest nodes, a changed node, a slot one node
    /// short, a padded slot, and a malformed set.
    #[test]
    fn merged_traversal_equals_the_reference_on_random_sets() {
        let t = tree();
        let hash = LegacyHashFn(h);
        let mut state = 0x1234_5678_9abc_def0u64;
        let mut next = || {
            state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        };
        for case in 0..200 {
            let k = 1 + (next() % MAX_MERGED as u64) as usize;
            let mut set: Vec<u32> = Vec::new();
            while set.len() < k {
                let base = (next() % (1 << LEAF_BITS)) as u32;
                for x in [base, base ^ 1] {
                    if set.len() < k && !set.contains(&x) && (x == base || next() % 3 == 0) {
                        set.push(x);
                    }
                }
            }
            set.sort();
            let nodes = merged_nodes(&t, &set);
            assert_eq!(nodes.len(), 32 * node_count_merged(&set).unwrap());
            let mut variants: Vec<Vec<u8>> = Vec::new();
            variants.push(nodes.clone());
            let mut changed = nodes.clone();
            if !changed.is_empty() {
                let at = (next() as usize) % changed.len();
                changed[at] ^= 1;
            }
            variants.push(changed);
            if nodes.len() >= 32 {
                variants.push(nodes[..nodes.len() - 32].to_vec());
            }
            let mut padded = nodes.clone();
            padded.extend_from_slice(&[0u8; 64]);
            variants.push(padded);
            for (v, slot) in variants.iter().enumerate() {
                let mut idx = [0u32; MAX_MERGED];
                let mut val = [[0u8; 32]; MAX_MERGED];
                idx[..k].copy_from_slice(&set);
                val[..k].copy_from_slice(&leaves(&set));
                let (mut idx2, mut val2) = (idx, val);
                let got = verify_counting_merged(hash, &t.root(), &mut idx, &mut val, k, slot);
                let want = reference_counting_merged(&t.root(), &mut idx2, &mut val2, k, slot);
                assert_eq!(got, want, "case {case} variant {v}");
                if v == 0 {
                    assert_eq!(got, Counted::Done { root_ok: true, used: nodes.len() }, "case {case}");
                }
            }
            if k >= 2 {
                let mut idx = [0u32; MAX_MERGED];
                let mut val = [[0u8; 32]; MAX_MERGED];
                idx[..k].copy_from_slice(&set);
                idx.swap(0, 1);
                assert_eq!(verify_counting_merged(hash, &t.root(), &mut idx, &mut val, k, &nodes), Counted::Malformed);
            }
        }
    }

    #[test]
    fn worst_case_counts() {
        let spread = |k: u32, bits: u32| -> Vec<u32> {
            let mut v: Vec<u32> = (0..k).map(|j| j.reverse_bits() >> (32 - bits)).collect();
            v.sort();
            v
        };
        assert_eq!(node_count(Arity::Two, &spread(10, 18)), Some(146));
        assert_eq!(node_count(Arity::Two, &spread(12, 18)), Some(172));
        assert_eq!(node_count(Arity::Two, &spread(10, 16)), Some(128));
        assert_eq!(node_count(Arity::Two, &spread(12, 16)), Some(150));
        assert_eq!(node_count(Arity::Eight, &spread(10, 18)), Some(334));
        assert_eq!(node_count(Arity::Eight, &spread(12, 18)), Some(388));
        assert_eq!(node_count(Arity::Eight, &spread(10, 16)), Some(292));
        assert_eq!(node_count(Arity::Eight, &spread(12, 16)), Some(346));
    }
}
