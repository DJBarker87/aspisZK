//! ADOPTED R1 VERIFIER (PREREG-PROOF-SIZE-2, 2026-10-19; prototype from the
//! proof-size feasibility test). UNPROVED: PROOF-SIZE-OBLIGATIONS-20261019.
//!
//! Two-transaction verifier for the fixed-length compact binary-multiproof
//! format (`crate::compact`), re-exported as `verifier::{tx1, tx2,
//! tx2_authenticated, parse_shape}`. Child module of `verifier`, so it reuses
//! the transcript, folding, accumulation, relation and checkpoint code
//! unchanged. Differences from the retired eight-way path
//! (`verifier::eight_way`, audit builds only), and nothing else:
//! - the stored proof is the compact format; semantic rows 14..26 and `y1`
//!   are expanded to their logical 32-byte form (zero high half) before any
//!   parse or hash, so every Fiat-Shamir message keeps its byte definition;
//! - C1, C2 and the folded tree are binary trees; authentication is one
//!   multiproof per tree per transaction batch (queries 0..SPLIT in stage 1,
//!   SPLIT..22 in stage 2), from fixed, zero-padded node slots;
//! - the checkpoint hashes the compact stored bytes.
use super::*;
use crate::compact::{self, CodecError, OPENING, SLOT_NODES, SPLIT};
use crate::multiproof::{self, Arity};
use aspis_core::state_only_private_merkle::private_leaf_hash_with_digest;

impl From<CodecError> for Error {
    fn from(_: CodecError) -> Self {
        Error::Parse
    }
}

#[inline(always)]
fn opening(proof: &[u8], i: usize) -> &[u8] {
    let at = compact::OFF_OPENINGS + i * OPENING;
    &proof[at..at + OPENING]
}
#[inline(always)]
fn slot(proof: &[u8], s: usize) -> &[u8] {
    &proof[compact::slot_offset(s)..compact::slot_offset(s + 1)]
}

/// Fixed length, magic, variant S2, zero header tail.
#[inline(never)]
pub fn parse_shape(proof: &[u8]) -> Result<Variant, Error> {
    if proof.len() != compact::PROOF_BYTES
        || &proof[..8] != compact::MAGIC
        || proof[8] != Variant::S2.tag()
        || proof[9..16].iter().any(|&x| x != 0)
    {
        return Err(Error::Parse);
    }
    Ok(Variant::S2)
}

/// The shipped strict scan for every field outside the semantic prefix
/// (the semantic prefix is checked by `Prefix::parse` after expansion).
#[inline(never)]
fn canonical_scan(proof: &[u8]) -> Result<(), Error> {
    compact::check_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE])?;
    echeck(&proof[compact::OFF_INACTIVE..compact::OFF_INACTIVE + 32], false)?;
    echeck(&proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT], false)?;
    echeck(&proof[compact::OFF_ROUND1..compact::OFF_OPENINGS], false)?;
    for i in 0..22 {
        let q = opening(proof, i);
        for s in 0..4 {
            for l in 0..26 {
                M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
            }
            K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
            for l in 0..2 {
                K::from_le_bytes(&q[480 + s * 32 + l * 16..480 + s * 32 + l * 16 + 16]).ok_or(Error::Parse)?;
            }
        }
        echeck(&q[672..800], false)?;
    }
    Ok(())
}

/// View over the logical semantic/y1 buffers and the stored wide fields.
fn wide_view<'a>(proof: &'a [u8], semantic: &'a [u8], y1: &'a [u8]) -> Result<View<'a>, Error> {
    Ok(View {
        variant: Variant::S2,
        semantic,
        y1,
        inactive: E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: Some(proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap()),
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: &[],
    })
}


#[inline(always)]
fn batch_keys(queries: &[u32; 22], lo: usize, n: usize, tree: usize) -> [u64; multiproof::MAX_BATCH] {
    let mut keys = [0u64; multiproof::MAX_BATCH];
    for j in 0..n {
        let u = queries[lo + j];
        let index = if tree == 2 { u / 4 } else { u };
        keys[j] = (u64::from(index) << 8) | j as u64;
    }
    keys
}


#[inline(always)]
fn sort_batch_keys(mut keys: [u64; multiproof::MAX_BATCH], n: usize) -> [u64; multiproof::MAX_BATCH] {
    for i in 1..n {
        let mut j = i;
        while j > 0 && batch_key_at(&keys, j - 1) > batch_key_at(&keys, j) {
            keys.swap(j - 1, j);
            j -= 1;
        }
    }
    keys
}


#[inline(always)]
fn batch_leaf<H: Digest32>(hash: H, tree: usize, q: &[u8]) -> [u8; 32] {
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


#[inline(always)]
fn same_batch_leaf(values: &[[u8; 32]; multiproof::MAX_BATCH], index: usize, leaf: [u8; 32]) -> bool {
    values[index] == leaf
}


#[inline(always)]
fn same_batch_index(values: &[u32; multiproof::MAX_BATCH], index: usize, expected: u32) -> bool {
    values[index] == expected
}


#[inline(always)]
fn batch_key_at(keys: &[u64; multiproof::MAX_BATCH], index: usize) -> u64 {
    keys[index]
}

/// Verify the three multiproofs of one batch. Indices are sorted as u64
/// keys (index << 8 | position) so leaf hashes are written once, in sorted
/// order; equal folded indices must carry identical leaves and are merged.
#[inline(never)]
fn batch_merkle<H: Digest32>(proof: &[u8], p: &Prepared, folded_root: &[u8; 32], batch: usize, hash: H) -> Result<(), Error> {
    let [root0, root1] = p.roots;
    batch_merkle_values(proof, p.queries, [root0, root1, *folded_root], batch, hash)
}

#[inline(always)]
fn batch_merkle_values<H: Digest32>(proof: &[u8], queries: [u32; 22], roots: [[u8; 32]; 3], batch: usize, hash: H) -> Result<(), Error> {
    let mut idx = [0u32; multiproof::MAX_BATCH];
    let mut val = [[0u8; 32]; multiproof::MAX_BATCH];
    let [root0, root1, root2] = roots;
    batch_tree(proof, queries, root0, batch, 0, &mut idx, &mut val, hash)?;
    batch_tree(proof, queries, root1, batch, 1, &mut idx, &mut val, hash)?;
    batch_tree(proof, queries, root2, batch, 2, &mut idx, &mut val, hash)?;
    Ok(())
}

#[inline(always)]
fn batch_tree<H: Digest32>(proof: &[u8], queries: [u32; 22], root: [u8; 32], batch: usize, tree: usize, idx: &mut [u32; multiproof::MAX_BATCH], val: &mut [[u8; 32]; multiproof::MAX_BATCH], hash: H) -> Result<(), Error> {
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

/// The shipped per-query folding and accumulation, reading the candidate
/// opening (C1/C2 values at the shipped offsets 0..608, folded values at
/// 672..800). Merkle authentication was done per batch.
#[inline(always)]
fn query_values(proof: &[u8], p: &Prepared, mut a: Accumulator, g: &[E; 29], obs: Observer, geometry: &QueryGeometry, mut pending: BatchedWeights) -> Result<(Accumulator, BatchedWeights), Error> {
    let i = a.next;
    let u = p.queries[i] as usize;
    let q = opening(proof, i);
    let dots = crate::fast_dots::four_dots(q, g);
    crate::trace::value(9, 4 * i, dots[0]);
    crate::trace::value(9, 4 * i + 1, dots[1]);
    crate::trace::value(9, 4 * i + 2, dots[2]);
    crate::trace::value(9, 4 * i + 3, dots[3]);
    let inverse = *geometry.for_query(i);
    let folded = circle_fold_with_inverses(p.alpha[0], dots, &inverse);
    crate::trace::value(10, 2 * i, folded);
    let values = core::array::from_fn(|s| field(&q[672..800], s));
    if folded != values[u % 4] {
        return Err(Error::Query);
    }
    let folded = line_fold_with_inverses(p.alpha[1], values, &inverse);
    crate::trace::value(10, 2 * i + 1, folded);
    let z = geometry.line_z[i - geometry.start];
    let node = z.mul(z).double().sub(M31::ONE);
    accumulate_batched_with_node(p, &mut a, node, folded, &mut pending);
    mark(obs, Phase::Query(i));
    Ok((a, pending))
}


#[inline(always)]
fn query_loop(proof: &[u8], p: &Prepared, mut a: Accumulator, g: &[E; 29], obs: Observer, geometry: &QueryGeometry, pending: BatchedWeights, end: usize) -> Result<(Accumulator, BatchedWeights), Error> {
    let mut state = Ok((a, pending));
    loop {
        match state {
            Err(error) => return Err(error),
            Ok((a, pending)) => {
                if a.next >= end {
                    return Ok((a, pending));
                }
                state = query_values(proof, p, a, g, obs, geometry, pending);
            }
        }
    }
}

#[inline(never)]
fn prepare<H: Digest32>(public: Public<'_>, proof: &[u8], hash: H, obs: Observer, g: &mut [E; 29]) -> Result<Box<Prepared>, Error> {
    let mut logical = aspis_core::r0::heap::filled(compact::LOGICAL_SEMANTIC + compact::LOGICAL_Y1, 0u8).map_err(|_| Error::Allocation)?;
    let (semantic, y1) = logical.split_at_mut(compact::LOGICAL_SEMANTIC);
    compact::expand_semantic(&proof[compact::OFF_SEMANTIC..compact::OFF_Y1], semantic)?;
    compact::expand_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE], y1)?;
    let v = wide_view(proof, &logical[..compact::LOGICAL_SEMANTIC], &logical[compact::LOGICAL_SEMANTIC..])?;
    let sem = crate::r1_semantic::verify_observed(public, v.semantic, hash, obs).map_err(|_| Error::Semantic)?;
    mark(obs, Phase::Semantic);
    Prepared::new(&sem, &v, hash, g)
}

/// Stage 1: strict parse of the whole stored proof, semantic layer,
/// challenges, batch-A multiproofs and queries 0..SPLIT; returns the
/// checkpoint over the compact stored bytes.
#[inline(never)]
pub fn tx1<H: Digest32>(public: Public<'_>, public_bytes: &[u8], proof: &[u8], k: usize, hash: H, obs: Observer) -> Result<Vec<u8>, Error> {
    if k != SPLIT {
        return Err(Error::Parse);
    }
    parse_shape(proof)?;
    canonical_scan(proof)?;
    mark(obs, Phase::Parsed);
    let mut g = [E::ZERO; 29];
    let p = prepare(public, proof, hash, obs, &mut g)?;
    let a = Accumulator::new(Variant::S2)?;
    mark(obs, Phase::Prepare);
    let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    batch_merkle(proof, &p, &folded_root, 0, hash)?;
    mark(obs, Phase::Merkle(0));
    let geometry = QueryGeometry::for_range(&p.queries, 0, k)?;
    let pending = BatchedWeights::new(&a.weights)?;
    let (mut a, pending) = query_loop(proof, &p, a, &g, obs, &geometry, pending, k)?;
    pending.finish(&mut a.weights);
    let bytes = checkpoint(&p, &a, proof, public_bytes, hash);
    mark(obs, Phase::CheckpointWrite);
    Ok(bytes)
}

#[inline(never)]
fn tx2_common<H: Digest32>(public_bytes: &[u8], proof: &[u8], checkpoint: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    let (p, a) = resume(checkpoint, proof, public_bytes, Variant::S2, hash)?;
    if a.next != SPLIT {
        return Err(Error::Checkpoint);
    }
    let g = powers::<29>(p.gamma);
    mark(obs, Phase::CheckpointRead);
    let inactive = E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?;
    let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    batch_merkle(proof, &p, &folded_root, 1, hash)?;
    mark(obs, Phase::Merkle(SPLIT));
    let geometry = QueryGeometry::for_range(&p.queries, a.next, 22)?;
    let pending = BatchedWeights::new(&a.weights)?;
    let (a, pending) = query_loop(proof, &p, a, &g, obs, &geometry, pending, 22)?;
    // End the loop accumulator borrow before finishing its weights.
    let Accumulator { mut weights, rhs, power, next } = a;
    pending.finish(&mut weights);
    let a = Accumulator { weights, rhs, power, next };
    // Construct only the relation view after the last proof-consuming loop.
    let v = View {
        variant: Variant::S2, semantic: &[], y1: &[], inactive,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: None,
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: &[],
    };
    finish_relation(&v, &p, &a, obs)
}

/// Stage 2 with checkpoint provenance established by the caller (Pool
/// route); same precondition as the shipped `tx2_authenticated`.
#[inline(never)]
pub fn tx2_authenticated<H: Digest32>(public_bytes: &[u8], proof: &[u8], checkpoint: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    parse_shape(proof)?;
    mark(obs, Phase::Parsed);
    tx2_common(public_bytes, proof, checkpoint, hash, obs)
}

/// Stage 2 repeating the full canonical scan.
#[inline(never)]
pub fn tx2<H: Digest32>(public_bytes: &[u8], proof: &[u8], checkpoint: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    parse_shape(proof)?;
    canonical_scan(proof)?;
    mark(obs, Phase::Parsed);
    tx2_common(public_bytes, proof, checkpoint, hash, obs)
}
