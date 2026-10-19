//! UNPROVED CANDIDATE (proof-size feasibility test, 2026-10-19).
//!
//! Two-transaction verifier for the fixed-length compact binary-multiproof
//! format (`crate::compact`). Child module of `verifier`, so it reuses the
//! shipped transcript, folding, accumulation, relation and checkpoint code
//! unchanged. Differences from the shipped path, and nothing else:
//! - the stored proof is the compact format; semantic rows 14..26 and `y1`
//!   are expanded to their logical 32-byte form (zero high half) before any
//!   parse or hash, so every Fiat-Shamir message keeps its shipped bytes;
//! - C1, C2 and the folded tree are binary trees (roots, hence challenges,
//!   differ from the eight-way proofs); authentication is one multiproof per
//!   tree per transaction batch (queries 0..SPLIT in stage 1, SPLIT..22 in
//!   stage 2), from fixed, zero-padded node slots;
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
    for c in proof[compact::OFF_Y1..compact::OFF_INACTIVE].chunks_exact(16) {
        K::from_le_bytes(c).ok_or(Error::Parse)?;
    }
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

/// Node count of one slot; error if over its fixed capacity.
fn slot_count(queries: &[u32], tree: usize) -> Result<(usize, [u32; multiproof::MAX_BATCH]), Error> {
    let mut idx = [0u32; multiproof::MAX_BATCH];
    let n = queries.len();
    for (o, &u) in idx.iter_mut().zip(queries) {
        *o = if tree == 2 { u / 4 } else { u };
    }
    // Sort only (count needs distinct sorted indices).
    let mut leaves = [[0u8; 32]; multiproof::MAX_BATCH];
    let d = multiproof::sort_dedup(&mut idx[..n], &mut leaves[..n]).ok_or(Error::Merkle)?;
    let count = multiproof::node_count(Arity::Two, &idx[..d]).ok_or(Error::Merkle)?;
    Ok((count, idx))
}

/// Every slot's padding (bytes after its node count) is zero.
#[inline(never)]
fn check_padding(proof: &[u8], queries: &[u32; 22]) -> Result<(), Error> {
    for (batch, range) in [(0, 0..SPLIT), (1, SPLIT..22)] {
        for tree in 0..3 {
            let s = 3 * batch + tree;
            let (count, _) = slot_count(&queries[range.clone()], tree)?;
            if count > SLOT_NODES[s] || slot(proof, s)[32 * count..].iter().any(|&b| b != 0) {
                return Err(Error::Parse);
            }
        }
    }
    Ok(())
}

/// Verify the three multiproofs of one batch.
#[inline(never)]
fn batch_merkle<H: Digest32>(proof: &[u8], p: &Prepared, folded_root: &[u8; 32], batch: usize, hash: H) -> Result<(), Error> {
    let range = if batch == 0 { 0..SPLIT } else { SPLIT..22 };
    let roots = [&p.roots[0], &p.roots[1], folded_root];
    for tree in 0..3 {
        let s = 3 * batch + tree;
        let mut idx = [0u32; multiproof::MAX_BATCH];
        let mut val = [[0u8; 32]; multiproof::MAX_BATCH];
        let n = range.len();
        for (j, i) in range.clone().enumerate() {
            let q = opening(proof, i);
            let u = p.queries[i];
            let (tag, values, salt, index) = match tree {
                0 => (merkle::C1_TAG, &q[..480], &q[608..640], u),
                1 => (merkle::C2_TAG, &q[480..608], &q[640..672], u),
                _ => (0x72, &q[672..800], &q[800..832], u / 4),
            };
            idx[j] = index;
            val[j] = private_leaf_hash_with_digest(hash, tag, values, salt.try_into().unwrap());
        }
        let d = multiproof::sort_dedup(&mut idx[..n], &mut val[..n]).ok_or(Error::Merkle)?;
        let count = multiproof::node_count(Arity::Two, &idx[..d]).ok_or(Error::Merkle)?;
        let nodes = slot(proof, s);
        if count > SLOT_NODES[s] || nodes[32 * count..].iter().any(|&b| b != 0) {
            return Err(Error::Parse);
        }
        if !multiproof::verify(hash, Arity::Two, roots[tree], &idx[..d], &val[..d], &nodes[..32 * count]) {
            return Err(Error::Merkle);
        }
    }
    Ok(())
}

/// The shipped per-query folding and accumulation, reading the candidate
/// opening (C1/C2 values at the shipped offsets 0..608, folded values at
/// 672..800). Merkle authentication was done per batch.
#[inline(never)]
fn query_values(proof: &[u8], p: &Prepared, a: &mut Accumulator, g: &[E; 29], obs: Observer, geometry: &QueryGeometry, pending: Option<&mut BatchedWeights>) -> Result<(), Error> {
    let i = a.next;
    let u = p.queries[i] as usize;
    let q = opening(proof, i);
    let dots = crate::fast_dots::four_dots(q, g);
    for s in 0..4 {
        crate::trace::value(9, 4 * i + s, dots[s]);
    }
    let inverse = geometry.for_query(i);
    let folded = circle_fold_with_inverses(p.alpha[0], dots, inverse);
    crate::trace::value(10, 2 * i, folded);
    let values = core::array::from_fn(|s| field(&q[672..800], s));
    if folded != values[u % 4] {
        return Err(Error::Query);
    }
    let folded = line_fold_with_inverses(p.alpha[1], values, inverse);
    crate::trace::value(10, 2 * i + 1, folded);
    let z = geometry.line_z[i - geometry.start];
    let node = z.mul(z).double().sub(M31::ONE);
    accumulate_with_node(p, a, node, folded, pending);
    mark(obs, Phase::Query(i));
    Ok(())
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
    check_padding(proof, &p.queries)?;
    let mut a = Accumulator::new(Variant::S2)?;
    mark(obs, Phase::Prepare);
    let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    batch_merkle(proof, &p, &folded_root, 0, hash)?;
    mark(obs, Phase::Merkle(0));
    let geometry = QueryGeometry::for_range(&p.queries, 0, k)?;
    let mut pending = BatchedWeights::new(&a.weights)?;
    while a.next < k {
        query_values(proof, &p, &mut a, &g, obs, &geometry, Some(&mut pending))?;
    }
    pending.finish(&mut a.weights);
    let bytes = checkpoint(&p, &a, proof, public_bytes, hash);
    mark(obs, Phase::CheckpointWrite);
    Ok(bytes)
}

#[inline(never)]
fn tx2_common<H: Digest32>(public_bytes: &[u8], proof: &[u8], checkpoint: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    let (p, mut a) = resume(checkpoint, proof, public_bytes, Variant::S2, hash)?;
    if a.next != SPLIT {
        return Err(Error::Checkpoint);
    }
    let g = powers::<29>(p.gamma);
    mark(obs, Phase::CheckpointRead);
    let v = wide_view(proof, &[], &[])?;
    batch_merkle(proof, &p, v.folded_root.unwrap(), 1, hash)?;
    mark(obs, Phase::Merkle(SPLIT));
    let geometry = QueryGeometry::for_range(&p.queries, a.next, 22)?;
    let mut pending = BatchedWeights::new(&a.weights)?;
    while a.next < 22 {
        query_values(proof, &p, &mut a, &g, obs, &geometry, Some(&mut pending))?;
    }
    pending.finish(&mut a.weights);
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
