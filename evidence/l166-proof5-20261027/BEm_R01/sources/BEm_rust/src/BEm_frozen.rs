// Generated exact source cuts; BEm_generate.py --check verifies provenance.
extern crate alloc;
extern crate self as aspis_core;
pub type Digest = [u8;32];
pub trait Digest32: Copy {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32];
}
pub mod r0 { pub mod merkle {
use crate::{Digest,Digest32};
pub const C1_TAG:u8=0x71; pub const C2_TAG:u8=0xf1;
pub fn parent_with_digest<H: Digest32>(hash: H, children: &[Digest; 8]) -> Digest {
    hash.digest(&[
        &[0x18],
        &children[0],
        &children[1],
        &children[2],
        &children[3],
        &children[4],
        &children[5],
        &children[6],
        &children[7],
    ])
}
} }
pub const STATE_ONLY_PRIVATE_LEAF_SALT_BYTES:usize=32;
pub const DOM_LEAF:u8=0x10;
pub fn private_leaf_hash_with_digest<H: Digest32>(
    hash: H,
    tree_tag: u8,
    value: &[u8],
    salt: &[u8; STATE_ONLY_PRIVATE_LEAF_SALT_BYTES],
) -> [u8; 32] {
    hash.digest(&[&[DOM_LEAF, tree_tag], value, salt])
}
pub mod state_only_private_merkle {pub use crate::private_leaf_hash_with_digest;}
pub mod compact {
pub const MAGIC: &[u8; 8] = b"R1P3CB18";
pub const HEADER: usize = 16;
pub const SPLIT: usize = 10;
pub const QUERIES: usize = 22;
pub const SEMANTIC_ROWS: u8 = 27;
/// Logical (shipped) semantic bytes: root 32 + 27 framed records.
pub const LOGICAL_SEMANTIC: usize = 13_831;
/// Values with an implied zero high half: rows 14..=26.
pub const SEMANTIC_COMPACT_VALUES: usize = 1 + 10 * 28 + (87 + 29) + 29;
pub const COMPACT_SEMANTIC: usize = LOGICAL_SEMANTIC - 16 * SEMANTIC_COMPACT_VALUES;
pub const COMPACT_Y1: usize = 29 * 16;
pub const LOGICAL_Y1: usize = 29 * 32;
pub const OPENING: usize = 480 + 128 + 32 + 32 + 128 + 32;
pub const OFF_SEMANTIC: usize = HEADER;
pub const OFF_Y1: usize = OFF_SEMANTIC + COMPACT_SEMANTIC;
pub const OFF_INACTIVE: usize = OFF_Y1 + COMPACT_Y1;
pub const OFF_ROUND0: usize = OFF_INACTIVE + 32;
pub const OFF_FOLDED_ROOT: usize = OFF_ROUND0 + 224;
pub const OFF_ROUND1: usize = OFF_FOLDED_ROOT + 32;
pub const OFF_FINAL: usize = OFF_ROUND1 + 224;
pub const FINAL_LEN: usize = 64;
pub const OFF_OPENINGS: usize = OFF_FINAL + FINAL_LEN * 32;
pub const OFF_NODES: usize = OFF_OPENINGS + QUERIES * OPENING;
/// Bytes before the multiproof nodes (28,359).
pub const FIXED: usize = OFF_NODES;
/// Worst-case supplied nodes over all query sets (S1 counting bound).
pub const MAX_NODES: usize = 2 * (146 + 172) + (128 + 150);
pub const MAX_PROOF: usize = FIXED + 32 * MAX_NODES;
/// Worst-case node counts per slot: [C1 A, C2 A, folded A, C1 B, C2 B, folded B].
pub const SLOT_NODES: [usize; 6] = [146, 146, 128, 172, 172, 150];
/// Byte offset of each slot inside the stored proof.
pub const fn slot_offset(slot: usize) -> usize {
    let mut at = OFF_NODES;
    let mut i = 0;
    while i < slot {
        at += 32 * SLOT_NODES[i];
        i += 1;
    }
    at
}
/// The candidate's one stored length.
pub const PROOF_BYTES: usize = MAX_PROOF;
const _: () = assert!(slot_offset(6) == MAX_PROOF);
const _: () = assert!(SEMANTIC_COMPACT_VALUES == 426 && COMPACT_SEMANTIC == 7015);
const _: () = assert!(FIXED == 28_359 && MAX_PROOF == 57_607);


}
pub mod multiproof {
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

// Evidence-only access to the unchanged first inner hash helpers.
#[cfg(kani)]
pub(crate) fn BEm_occupied<H: Digest32>(hash: H, values: &[[u8;32];MAX_BATCH], index: usize) -> [u8;32] {
    occupied_binary_parent(hash, values, index)
}
#[cfg(kani)]
pub(crate) fn BEm_sibling<H: Digest32>(hash: H, values: &[[u8;32];MAX_BATCH], index: usize, sibling: &[u8], left: bool) -> [u8;32] {
    sibling_binary_parent(hash, values, index, sibling, left)
}

}
pub mod shipped {
use crate::{Digest32,compact::{self,OPENING,SPLIT,SLOT_NODES},multiproof::{self,Arity}};
use crate::{r0::merkle,private_leaf_hash_with_digest};
#[derive(Clone,Copy,Debug,PartialEq,Eq)] pub enum Error {Merkle,Parse}
pub(crate) fn opening(proof: &[u8], i: usize) -> &[u8] {
    let at = compact::OFF_OPENINGS + i * OPENING;
    &proof[at..at + OPENING]
}
pub(crate) fn slot(proof: &[u8], s: usize) -> &[u8] {
    &proof[compact::slot_offset(s)..compact::slot_offset(s + 1)]
}
pub(crate) fn batch_keys(queries: &[u32; 22], lo: usize, n: usize, tree: usize) -> [u64; multiproof::MAX_BATCH] {
    let mut keys = [0u64; multiproof::MAX_BATCH];
    for j in 0..n {
        let u = queries[lo + j];
        let index = if tree == 2 { u / 4 } else { u };
        keys[j] = (u64::from(index) << 8) | j as u64;
    }
    keys
}
pub(crate) fn sort_batch_keys(mut keys: [u64; multiproof::MAX_BATCH], n: usize) -> [u64; multiproof::MAX_BATCH] {
    for i in 1..n {
        let mut j = i;
        while j > 0 && batch_key_at(&keys, j - 1) > batch_key_at(&keys, j) {
            keys.swap(j - 1, j);
            j -= 1;
        }
    }
    keys
}
pub(crate) fn batch_leaf<H: Digest32>(hash: H, tree: usize, q: &[u8]) -> [u8; 32] {
    match tree {
        0 => {
            let salt: [u8; 32] = q[608..640].try_into().unwrap();
            private_leaf_hash_with_digest(hash, merkle::C1_TAG, &q[..480], &salt)
        }
        1 => {
            let salt: [u8; 32] = q[640..672].try_into().unwrap();
            private_leaf_hash_with_digest(hash, merkle::C2_TAG, &q[480..608], &salt)
        }
        _ => {
            let salt: [u8; 32] = q[800..832].try_into().unwrap();
            private_leaf_hash_with_digest(hash, 0x72, &q[672..800], &salt)
        }
    }
}
pub(crate) fn same_batch_leaf(values: &[[u8; 32]; multiproof::MAX_BATCH], index: usize, leaf: [u8; 32]) -> bool {
    values[index] == leaf
}
pub(crate) fn same_batch_index(values: &[u32; multiproof::MAX_BATCH], index: usize, expected: u32) -> bool {
    values[index] == expected
}
pub(crate) fn batch_key_at(keys: &[u64; multiproof::MAX_BATCH], index: usize) -> u64 {
    keys[index]
}
pub(crate) fn batch_merkle_values<H: Digest32>(proof: &[u8], queries: [u32; 22], roots: [[u8; 32]; 3], batch: usize, hash: H) -> Result<(), Error> {
    let mut idx = [0u32; multiproof::MAX_BATCH];
    let mut val = [[0u8; 32]; multiproof::MAX_BATCH];
    let [root0, root1, root2] = roots;
    batch_tree(proof, queries, root0, batch, 0, &mut idx, &mut val, hash)?;
    batch_tree(proof, queries, root1, batch, 1, &mut idx, &mut val, hash)?;
    batch_tree(proof, queries, root2, batch, 2, &mut idx, &mut val, hash)?;
    Ok(())
}
pub(crate) fn batch_tree<H: Digest32>(proof: &[u8], queries: [u32; 22], root: [u8; 32], batch: usize, tree: usize, idx: &mut [u32; multiproof::MAX_BATCH], val: &mut [[u8; 32]; multiproof::MAX_BATCH], hash: H) -> Result<(), Error> {
    let (lo, hi) = if batch == 0 { (0, SPLIT) } else { (SPLIT, 22) };
    let n = hi - lo;
    let s = 3 * batch + tree;
    let keys = sort_batch_keys(batch_keys(&queries, lo, n, tree), n);
    let mut d = 0;
    let mut key_position = 0;
    while key_position < n {
        let key = batch_key_at(&keys, key_position);
        key_position += 1;
        let index = (key >> 8) as u32;
        let q = opening(proof, lo + (key & 0xff) as usize);
        let leaf = batch_leaf(hash, tree, q);
        if d > 0 && same_batch_index(idx, d - 1, index) {
            if !same_batch_leaf(val, d - 1, leaf) {
                return Err(Error::Merkle);
            }
            continue;
        }
        idx[d] = index;
        val[d] = leaf;
        d += 1;
    }
    let count = multiproof::node_count(Arity::Two, &idx[..d]).ok_or(Error::Merkle)?;
    let nodes = slot(proof, s);
    // Padding is whole 32-byte words: scan it 8 bytes at a time.
    if count > SLOT_NODES[s] || nodes[32 * count..].chunks_exact(8).any(|w| u64::from_le_bytes(w.try_into().unwrap()) != 0) {
        return Err(Error::Parse);
    }
    if !multiproof::verify_in_place(hash, Arity::Two, &root, idx, val, d, &nodes[..32 * count]) {
        return Err(Error::Merkle);
    }
    Ok(())
}
pub(crate) fn leaf_step<H:Digest32>(keys:[u64;16],mut key_position:usize,lo:usize,tree:usize,q:&[u8],idx:&mut [u32;16],val:&mut [[u8;32];16],mut d:usize,hash:H)->(bool,usize,usize,usize) {
        let key = batch_key_at(&keys, key_position);
        key_position += 1;
        let index = (key >> 8) as u32;
        let selected = lo + (key & 0xff) as usize;
        let leaf = batch_leaf(hash, tree, q);
        if d > 0 && same_batch_index(idx, d - 1, index) {
            if !same_batch_leaf(val, d - 1, leaf) {
                return (false,key_position,selected,d);
            }
            return (true,key_position,selected,d);
        }
        idx[d] = index;
        val[d] = leaf;
        d += 1;

(true,key_position,selected,d)
}

pub(crate) fn leaf_loop<H:Digest32>(proof:&[u8],keys:[u64;16],lo:usize,n:usize,tree:usize,idx:&mut [u32;16],val:&mut [[u8;32];16],hash:H)->(Result<(),Error>,usize) {
    let mut d = 0;
    let mut key_position = 0;
    while key_position < n {
        let key = batch_key_at(&keys, key_position);
        key_position += 1;
        let index = (key >> 8) as u32;
        let q = opening(proof, lo + (key & 0xff) as usize);
        let leaf = batch_leaf(hash, tree, q);
        if d > 0 && same_batch_index(idx, d - 1, index) {
            if !same_batch_leaf(val, d - 1, leaf) {
                return (Err(Error::Merkle),d);
            }
            continue;
        }
        idx[d] = index;
        val[d] = leaf;
        d += 1;
    }

(Ok(()),d)
}

}
