//! The shipped honest builder of the pair-forest semantic C1 trace (LOG D68.2).
//!
//! Every C1 cell of the forest compilation is written by the extracted copies
//! that the Lean theorem `builder_witness_merged` (R0Z/BuilderWitnessMerged.lean)
//! is about:
//!   * `aspis-r0-poseidon-copy`   (refine/poseidon)     — the permutation rounds;
//!   * `aspis-r0-block-writer-copies` (refine/blockwriters) — block, node, sponge;
//!   * `aspis-r0-writer-copies`   (refine/writers)      — value/occupancy aux,
//!     path aux, the bank-merge check and copy.
//! Their `src/lib.rs` files are the pinned extraction inputs and are used
//! unchanged.  The glue that composes them is the Lean glue `copyCellMerged`:
//!   * the table-driven part is `include!`d from the generated
//!     `refine/diffharness/tests/glue_gen.rs` (gen-glue.py.txt renders the same
//!     table as the Lean text it checks verbatim);
//!   * the structural part between the two `---------- ... ----------` markers
//!     below is a verbatim copy of `refine/diffharness/tests/glue.rs`, one Rust
//!     function per Lean definition (checked by
//!     `refine/migration/check-glue-text.py.txt`);
//!   * `merged_banks` is the loop of glue.rs `merged_trace`, returning both
//!     banks and the merge instead of the 29 comparison columns;
//!   * `records` is glue.rs `records` with the public asset in place of the
//!     test asset 77.
//! This module only computes cells and digests.  Witness and public
//! validation, and the error order, stay in `pair_forest_trace`.
#![allow(clippy::all)]

use alloc::{boxed::Box, vec::Vec};

use aspis_core::field::{M31, P};
use aspis_r0_block_writer_copies as bw;
use aspis_r0_writer_copies as cp;

use crate::poseidon2::Digest;

use super::{
    pair_forest_trace::PoolV1PairForestInputNoteWitnessV1, pair_trace::pair_empty_roots,
    pair_tree_profile::PoolV1PairLiveSnapshotV1, payment_relation::PoolV1OutputNoteWitnessV1,
};

fn raw(d: &Digest) -> [u32; 8] {
    core::array::from_fn(|i| d[i].0)
}

// ---------- the records (Lean RustWitness / RustPublic) ----------

#[derive(Clone)]
struct RW {
    input_value: u32,
    output_value: u32,
    change_value: u32,
    sk: [u32; 8],
    salt: [u32; 8],
    bits: [u32; 24],
    sibs: [[u32; 8]; 24],
    pair_first: [u32; 8],
    pair_occupied: u32,
    pair_second: [u32; 8],
    pair_inverse: u32,
    recipient_owner: [u32; 8],
    recipient_salt: [u32; 8],
    change_owner: [u32; 8],
    change_salt: [u32; 8],
}

#[derive(Clone)]
struct RP {
    transfer: bool,
    asset: u32,
    next_pair_index: u64,
    frontier: [[u32; 8]; 20],
    empty: [[u32; 8]; 20],
}

const ZERO8: [u32; 8] = [0; 8];

// ---------- structural glue: one function per Lean definition ----------

fn perm(pre: &[u32; 16], ab: &[u32; 16]) -> [[u32; 16]; 11] { aspis_r0_poseidon_copy::perm_rounds(pre, ab) }
/// spongeStep
fn sponge_step(pre: [u32; 16], chunk: [u32; 8], clen: usize) -> [u32; 16] {
    let ab = bw::sponge_absorb(&chunk, clen);
    perm(&pre, &ab)[10]
}
/// digest8
fn digest8(s: [u32; 16]) -> [u32; 8] { core::array::from_fn(|i| s[i]) }
/// blockDigestR
fn block_digest_r(pre: [u32; 16], ab: [u32; 16]) -> [u32; 8] { digest8(perm(&pre, &ab)[10]) }
/// spongeDigestR
fn sponge_digest_r(pre: [u32; 16], chunk: [u32; 8], clen: usize) -> [u32; 8] {
    block_digest_r(pre, bw::sponge_absorb(&chunk, clen))
}
/// nodeDigestR
fn node_digest_r(left: [u32; 8], right: [u32; 8]) -> [u32; 8] {
    block_digest_r(bw::node_pre(&right), bw::node_absorb(&left))
}
/// ownerD
fn owner_d(w: &RW) -> [u32; 8] { sponge_digest_r(init_owner(), w.sk, 8) }
/// noteC2R
fn note_c2r(value: u32, asset: u32, salt: &[u32; 8]) -> [u32; 8] {
    core::array::from_fn(|j| if j == 0 { value } else if j == 1 { asset } else { salt[j - 2] })
}
/// noteC3R
fn note_c3r(salt: &[u32; 8]) -> [u32; 8] {
    core::array::from_fn(|j| if j == 0 { salt[6] } else if j == 1 { salt[7] } else { 0 })
}
/// noteDigestR (chunksOf)
fn note_digest_r(w: &RW, p: &RP, h3: usize) -> [u32; 8] { sponge_digest_r(sponge_pre(w, p, h3), schunk(w, p, h3), sclen(h3)) }
fn input_leaf_r(w: &RW, p: &RP) -> [u32; 8] { note_digest_r(w, p, 3) }
fn recip_dr(w: &RW, p: &RP) -> [u32; 8] { note_digest_r(w, p, 29) }
fn change_dr(w: &RW, p: &RP) -> [u32; 8] { note_digest_r(w, p, 32) }
/// orderedR
fn ordered_r(cur: [u32; 8], sib: [u32; 8], b: bool) -> ([u32; 8], [u32; 8]) { if b { (sib, cur) } else { (cur, sib) } }
/// bitB
fn bit_b(w: &RW, l: usize) -> bool { w.bits[l] != 0 }
/// treeCurR
fn tree_cur_r(w: &RW, p: &RP, n: usize) -> [u32; 8] {
    if n == 0 { input_leaf_r(w, p) } else {
        let c = tree_cur_r(w, p, n - 1);
        let o = ordered_r(c, w.sibs[n - 1], bit_b(w, n - 1));
        node_digest_r(o.0, o.1)
    }
}
/// outPairR
fn out_pair_r(w: &RW, p: &RP) -> [u32; 8] {
    if p.transfer { node_digest_r(recip_dr(w, p), change_dr(w, p)) } else { node_digest_r(change_dr(w, p), ZERO8) }
}
/// appBitR
fn app_bit_r(p: &RP, n: usize) -> bool { ((p.next_pair_index >> n) & 1) != 0 }
/// appSibR
fn app_sib_r(p: &RP, n: usize) -> [u32; 8] { if app_bit_r(p, n) { p.frontier[n] } else { p.empty[n] } }
/// appCurR
fn app_cur_r(w: &RW, p: &RP, n: usize) -> [u32; 8] {
    if n == 0 { out_pair_r(w, p) } else {
        let c = app_cur_r(w, p, n - 1);
        let o = ordered_r(c, app_sib_r(p, n - 1), app_bit_r(p, n - 1));
        node_digest_r(o.0, o.1)
    }
}
/// NodeKind / ZeroKind
fn node_kind(h: usize) -> bool { (4..=24).contains(&h) || (33..=56).contains(&h) }
fn zero_kind(p: &RP, h: usize) -> bool { !p.transfer && (27..=29).contains(&h) }
/// RustWriterChain over rustChunks
fn rust_writer_chain(w: &RW, p: &RP, h: usize) -> [u32; 256] {
    if node_kind(h) {
        let (l, r) = children(w, p, h);
        let pre = bw::node_pre(&r);
        let ab = bw::node_absorb(&l);
        bw::write_block(&pre, &ab, &perm(&pre, &ab))
    } else if zero_kind(p, h) {
        let z = [0u32; 16];
        bw::write_block(&z, &z, &perm(&z, &z))
    } else {
        let pre = sponge_pre(w, p, h);
        let ab = bw::sponge_absorb(&schunk(w, p, h), sclen(h));
        bw::write_block(&pre, &ab, &perm(&pre, &ab))
    }
}
/// invR: x^(p-2) mod p
fn inv_r(x: u32) -> u32 {
    let (mut b, mut e, mut acc) = (x as u64 % P as u64, (P - 2) as u64, 1u64);
    while e > 0 {
        if e & 1 == 1 { acc = acc * b % P as u64; }
        b = b * b % P as u64;
        e >>= 1;
    }
    acc as u32
}
/// curArr / leftArr / rightArr (levelPair)
fn path_arrays(w: &RW, p: &RP) -> ([[u32; 8]; 24], [[u32; 8]; 24], [[u32; 8]; 24]) {
    let cur: [[u32; 8]; 24] = core::array::from_fn(|l| tree_cur_r(w, p, l));
    let lr: [([u32; 8], [u32; 8]); 24] = core::array::from_fn(|l| ordered_r(cur[l], w.sibs[l], bit_b(w, l)));
    (cur, core::array::from_fn(|l| lr[l].0), core::array::from_fn(|l| lr[l].1))
}
/// inRec / outRec
fn in_rec(w: &RW) -> cp::OccRecord {
    cp::OccRecord { occupied: w.pair_occupied, inverse: w.pair_inverse, commitment: w.pair_second,
        selected: w.bits[0], has_selected: true }
}
fn out_rec(w: &RW, p: &RP) -> cp::OccRecord {
    if p.transfer {
        let c = change_dr(w, p);
        cp::OccRecord { occupied: 1, inverse: inv_r(c[7]), commitment: c, selected: 0, has_selected: false }
    } else {
        cp::OccRecord { occupied: 0, inverse: 0, commitment: ZERO8, selected: 0, has_selected: false }
    }
}

/// The components of copyCell (blockR, pathR, auxR), computed once.
struct Parts { blocks: Vec<[u32; 256]>, path: Box<[u32; cp::PATH_BLOCK_CELLS]>, aux: [u32; 256] }

fn parts(w: &RW, p: &RP) -> Parts {
    let blocks = (0..57).map(|h| rust_writer_chain(w, p, h)).collect();
    let (cur, l, r) = path_arrays(w, p);
    let path = Box::new(cp::write_path_block(w.bits, cur, l, r));
    let aux = cp::write_aux_block([w.input_value, w.output_value, w.change_value], in_rec(w), out_rec(w, p));
    Parts { blocks, path, aux }
}
/// copyCell
fn copy_cell(pt: &Parts, c: usize, r: usize) -> u32 {
    if c < C1_COLS {
        if r < PATH_ROW0 { pt.blocks[r / 16][(r % 16) * 16 + c] }
        else if r < AUX_ROW0 { pt.path[(r - PATH_ROW0) * 16 + c] }
        else { pt.aux[(r - AUX_ROW0) * 16 + c] }
    } else { 0 }
}
fn late_row(k: usize) -> bool { (544..864).contains(&(k % 1024)) }

/// stableBank / lateBank / mergedR: the loop of glue.rs `merged_trace`, returning
/// the merge-check verdict, both banks and the merged trace (column-major flat).
fn merged_banks(w: &RW, p: &RP) -> (bool, Box<[u32; cp::TRACE_CELLS]>, Box<[u32; cp::TRACE_CELLS]>, Box<[u32; cp::TRACE_CELLS]>) {
    let pt = parts(w, p);
    let mut stable = Box::new([0u32; cp::TRACE_CELLS]);
    let mut late = Box::new([0u32; cp::TRACE_CELLS]);
    for k in 0..cp::TRACE_CELLS {
        stable[k] = if late_row(k) { 0 } else { copy_cell(&pt, k / 1024, k % 1024) };
        late[k] = if late_row(k) { pt.blocks[k % 1024 / 16][(k % 1024 % 16) * 16 + k / 1024] } else { 0 };
    }
    let ok = cp::merge_check(&stable, &late);
    let merged = Box::new(cp::merge_copy(&stable, &late));
    (ok, stable, late, merged)
}

include!("../../../../docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs");

// ---------- the Wspend⁺ → record map on the Rust side ----------

fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&PoolV1OutputNoteWitnessV1>,
           chg: &PoolV1OutputNoteWitnessV1, snapshot: &PoolV1PairLiveSnapshotV1, asset: M31) -> (RW, RP) {
    let rec = match rec { Some(r) => Some(*r), None => None };
    let input = *input;
    let chg = *chg;
    let snapshot = *snapshot;
    let pair = input.pair;
    let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
    let mut bits = [0u32; 24];
    let mut sibs = [[0u32; 8]; 24];
    bits[0] = u32::from(pair.selected_second);
    sibs[0] = [other[0].0, other[1].0, other[2].0, other[3].0, other[4].0, other[5].0, other[6].0, other[7].0];
    bits[1] = ((pair.membership.index >> 0) & 1) as u32;
    sibs[1] = [pair.membership.siblings[0][0].0, pair.membership.siblings[0][1].0, pair.membership.siblings[0][2].0, pair.membership.siblings[0][3].0, pair.membership.siblings[0][4].0, pair.membership.siblings[0][5].0, pair.membership.siblings[0][6].0, pair.membership.siblings[0][7].0];
    bits[2] = ((pair.membership.index >> 1) & 1) as u32;
    sibs[2] = [pair.membership.siblings[1][0].0, pair.membership.siblings[1][1].0, pair.membership.siblings[1][2].0, pair.membership.siblings[1][3].0, pair.membership.siblings[1][4].0, pair.membership.siblings[1][5].0, pair.membership.siblings[1][6].0, pair.membership.siblings[1][7].0];
    bits[3] = ((pair.membership.index >> 2) & 1) as u32;
    sibs[3] = [pair.membership.siblings[2][0].0, pair.membership.siblings[2][1].0, pair.membership.siblings[2][2].0, pair.membership.siblings[2][3].0, pair.membership.siblings[2][4].0, pair.membership.siblings[2][5].0, pair.membership.siblings[2][6].0, pair.membership.siblings[2][7].0];
    bits[4] = ((pair.membership.index >> 3) & 1) as u32;
    sibs[4] = [pair.membership.siblings[3][0].0, pair.membership.siblings[3][1].0, pair.membership.siblings[3][2].0, pair.membership.siblings[3][3].0, pair.membership.siblings[3][4].0, pair.membership.siblings[3][5].0, pair.membership.siblings[3][6].0, pair.membership.siblings[3][7].0];
    bits[5] = ((pair.membership.index >> 4) & 1) as u32;
    sibs[5] = [pair.membership.siblings[4][0].0, pair.membership.siblings[4][1].0, pair.membership.siblings[4][2].0, pair.membership.siblings[4][3].0, pair.membership.siblings[4][4].0, pair.membership.siblings[4][5].0, pair.membership.siblings[4][6].0, pair.membership.siblings[4][7].0];
    bits[6] = ((pair.membership.index >> 5) & 1) as u32;
    sibs[6] = [pair.membership.siblings[5][0].0, pair.membership.siblings[5][1].0, pair.membership.siblings[5][2].0, pair.membership.siblings[5][3].0, pair.membership.siblings[5][4].0, pair.membership.siblings[5][5].0, pair.membership.siblings[5][6].0, pair.membership.siblings[5][7].0];
    bits[7] = ((pair.membership.index >> 6) & 1) as u32;
    sibs[7] = [pair.membership.siblings[6][0].0, pair.membership.siblings[6][1].0, pair.membership.siblings[6][2].0, pair.membership.siblings[6][3].0, pair.membership.siblings[6][4].0, pair.membership.siblings[6][5].0, pair.membership.siblings[6][6].0, pair.membership.siblings[6][7].0];
    bits[8] = ((pair.membership.index >> 7) & 1) as u32;
    sibs[8] = [pair.membership.siblings[7][0].0, pair.membership.siblings[7][1].0, pair.membership.siblings[7][2].0, pair.membership.siblings[7][3].0, pair.membership.siblings[7][4].0, pair.membership.siblings[7][5].0, pair.membership.siblings[7][6].0, pair.membership.siblings[7][7].0];
    bits[9] = ((pair.membership.index >> 8) & 1) as u32;
    sibs[9] = [pair.membership.siblings[8][0].0, pair.membership.siblings[8][1].0, pair.membership.siblings[8][2].0, pair.membership.siblings[8][3].0, pair.membership.siblings[8][4].0, pair.membership.siblings[8][5].0, pair.membership.siblings[8][6].0, pair.membership.siblings[8][7].0];
    bits[10] = ((pair.membership.index >> 9) & 1) as u32;
    sibs[10] = [pair.membership.siblings[9][0].0, pair.membership.siblings[9][1].0, pair.membership.siblings[9][2].0, pair.membership.siblings[9][3].0, pair.membership.siblings[9][4].0, pair.membership.siblings[9][5].0, pair.membership.siblings[9][6].0, pair.membership.siblings[9][7].0];
    bits[11] = ((pair.membership.index >> 10) & 1) as u32;
    sibs[11] = [pair.membership.siblings[10][0].0, pair.membership.siblings[10][1].0, pair.membership.siblings[10][2].0, pair.membership.siblings[10][3].0, pair.membership.siblings[10][4].0, pair.membership.siblings[10][5].0, pair.membership.siblings[10][6].0, pair.membership.siblings[10][7].0];
    bits[12] = ((pair.membership.index >> 11) & 1) as u32;
    sibs[12] = [pair.membership.siblings[11][0].0, pair.membership.siblings[11][1].0, pair.membership.siblings[11][2].0, pair.membership.siblings[11][3].0, pair.membership.siblings[11][4].0, pair.membership.siblings[11][5].0, pair.membership.siblings[11][6].0, pair.membership.siblings[11][7].0];
    bits[13] = ((pair.membership.index >> 12) & 1) as u32;
    sibs[13] = [pair.membership.siblings[12][0].0, pair.membership.siblings[12][1].0, pair.membership.siblings[12][2].0, pair.membership.siblings[12][3].0, pair.membership.siblings[12][4].0, pair.membership.siblings[12][5].0, pair.membership.siblings[12][6].0, pair.membership.siblings[12][7].0];
    bits[14] = ((pair.membership.index >> 13) & 1) as u32;
    sibs[14] = [pair.membership.siblings[13][0].0, pair.membership.siblings[13][1].0, pair.membership.siblings[13][2].0, pair.membership.siblings[13][3].0, pair.membership.siblings[13][4].0, pair.membership.siblings[13][5].0, pair.membership.siblings[13][6].0, pair.membership.siblings[13][7].0];
    bits[15] = ((pair.membership.index >> 14) & 1) as u32;
    sibs[15] = [pair.membership.siblings[14][0].0, pair.membership.siblings[14][1].0, pair.membership.siblings[14][2].0, pair.membership.siblings[14][3].0, pair.membership.siblings[14][4].0, pair.membership.siblings[14][5].0, pair.membership.siblings[14][6].0, pair.membership.siblings[14][7].0];
    bits[16] = ((pair.membership.index >> 15) & 1) as u32;
    sibs[16] = [pair.membership.siblings[15][0].0, pair.membership.siblings[15][1].0, pair.membership.siblings[15][2].0, pair.membership.siblings[15][3].0, pair.membership.siblings[15][4].0, pair.membership.siblings[15][5].0, pair.membership.siblings[15][6].0, pair.membership.siblings[15][7].0];
    bits[17] = ((pair.membership.index >> 16) & 1) as u32;
    sibs[17] = [pair.membership.siblings[16][0].0, pair.membership.siblings[16][1].0, pair.membership.siblings[16][2].0, pair.membership.siblings[16][3].0, pair.membership.siblings[16][4].0, pair.membership.siblings[16][5].0, pair.membership.siblings[16][6].0, pair.membership.siblings[16][7].0];
    bits[18] = ((pair.membership.index >> 17) & 1) as u32;
    sibs[18] = [pair.membership.siblings[17][0].0, pair.membership.siblings[17][1].0, pair.membership.siblings[17][2].0, pair.membership.siblings[17][3].0, pair.membership.siblings[17][4].0, pair.membership.siblings[17][5].0, pair.membership.siblings[17][6].0, pair.membership.siblings[17][7].0];
    bits[19] = ((pair.membership.index >> 18) & 1) as u32;
    sibs[19] = [pair.membership.siblings[18][0].0, pair.membership.siblings[18][1].0, pair.membership.siblings[18][2].0, pair.membership.siblings[18][3].0, pair.membership.siblings[18][4].0, pair.membership.siblings[18][5].0, pair.membership.siblings[18][6].0, pair.membership.siblings[18][7].0];
    bits[20] = ((pair.membership.index >> 19) & 1) as u32;
    sibs[20] = [pair.membership.siblings[19][0].0, pair.membership.siblings[19][1].0, pair.membership.siblings[19][2].0, pair.membership.siblings[19][3].0, pair.membership.siblings[19][4].0, pair.membership.siblings[19][5].0, pair.membership.siblings[19][6].0, pair.membership.siblings[19][7].0];
    bits[21] = u32::from(input.super_root_directions[0]);
    sibs[21] = [input.super_root_siblings[0][0].0, input.super_root_siblings[0][1].0, input.super_root_siblings[0][2].0, input.super_root_siblings[0][3].0, input.super_root_siblings[0][4].0, input.super_root_siblings[0][5].0, input.super_root_siblings[0][6].0, input.super_root_siblings[0][7].0];
    bits[22] = u32::from(input.super_root_directions[1]);
    sibs[22] = [input.super_root_siblings[1][0].0, input.super_root_siblings[1][1].0, input.super_root_siblings[1][2].0, input.super_root_siblings[1][3].0, input.super_root_siblings[1][4].0, input.super_root_siblings[1][5].0, input.super_root_siblings[1][6].0, input.super_root_siblings[1][7].0];
    bits[23] = u32::from(input.super_root_directions[2]);
    sibs[23] = [input.super_root_siblings[2][0].0, input.super_root_siblings[2][1].0, input.super_root_siblings[2][2].0, input.super_root_siblings[2][3].0, input.super_root_siblings[2][4].0, input.super_root_siblings[2][5].0, input.super_root_siblings[2][6].0, input.super_root_siblings[2][7].0];
    let empty = pair_empty_roots();
    let (recipient_key, recipient_note_salt, transfer) = match rec {
        Some(r) => (r.owner_key, r.salt, true),
        None => ([M31(0); 8], [M31(0); 8], false),
    };
    let recipient_owner = [recipient_key[0].0, recipient_key[1].0, recipient_key[2].0, recipient_key[3].0, recipient_key[4].0, recipient_key[5].0, recipient_key[6].0, recipient_key[7].0];
    let recipient_salt = [recipient_note_salt[0].0, recipient_note_salt[1].0, recipient_note_salt[2].0, recipient_note_salt[3].0, recipient_note_salt[4].0, recipient_note_salt[5].0, recipient_note_salt[6].0, recipient_note_salt[7].0];
    let w = RW {
        input_value: pair.value,
        output_value: out,
        change_value: chg.value,
        sk: [pair.nullifier_key[0].0, pair.nullifier_key[1].0, pair.nullifier_key[2].0, pair.nullifier_key[3].0, pair.nullifier_key[4].0, pair.nullifier_key[5].0, pair.nullifier_key[6].0, pair.nullifier_key[7].0],
        salt: [pair.salt[0].0, pair.salt[1].0, pair.salt[2].0, pair.salt[3].0, pair.salt[4].0, pair.salt[5].0, pair.salt[6].0, pair.salt[7].0],
        bits,
        sibs,
        pair_first: [pair.pair_leaf.first_commitment[0].0, pair.pair_leaf.first_commitment[1].0, pair.pair_leaf.first_commitment[2].0, pair.pair_leaf.first_commitment[3].0, pair.pair_leaf.first_commitment[4].0, pair.pair_leaf.first_commitment[5].0, pair.pair_leaf.first_commitment[6].0, pair.pair_leaf.first_commitment[7].0],
        pair_occupied: pair.pair_leaf.second_occupied.0,
        pair_second: [pair.pair_leaf.second_commitment[0].0, pair.pair_leaf.second_commitment[1].0, pair.pair_leaf.second_commitment[2].0, pair.pair_leaf.second_commitment[3].0, pair.pair_leaf.second_commitment[4].0, pair.pair_leaf.second_commitment[5].0, pair.pair_leaf.second_commitment[6].0, pair.pair_leaf.second_commitment[7].0],
        pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
        recipient_owner,
        recipient_salt,
        change_owner: [chg.owner_key[0].0, chg.owner_key[1].0, chg.owner_key[2].0, chg.owner_key[3].0, chg.owner_key[4].0, chg.owner_key[5].0, chg.owner_key[6].0, chg.owner_key[7].0],
        change_salt: [chg.salt[0].0, chg.salt[1].0, chg.salt[2].0, chg.salt[3].0, chg.salt[4].0, chg.salt[5].0, chg.salt[6].0, chg.salt[7].0],
    };
    let p = RP {
        transfer,
        asset: asset.0,
        next_pair_index: snapshot.next_pair_index,
        frontier: [
            [snapshot.frontier[0][0].0, snapshot.frontier[0][1].0, snapshot.frontier[0][2].0, snapshot.frontier[0][3].0, snapshot.frontier[0][4].0, snapshot.frontier[0][5].0, snapshot.frontier[0][6].0, snapshot.frontier[0][7].0],
            [snapshot.frontier[1][0].0, snapshot.frontier[1][1].0, snapshot.frontier[1][2].0, snapshot.frontier[1][3].0, snapshot.frontier[1][4].0, snapshot.frontier[1][5].0, snapshot.frontier[1][6].0, snapshot.frontier[1][7].0],
            [snapshot.frontier[2][0].0, snapshot.frontier[2][1].0, snapshot.frontier[2][2].0, snapshot.frontier[2][3].0, snapshot.frontier[2][4].0, snapshot.frontier[2][5].0, snapshot.frontier[2][6].0, snapshot.frontier[2][7].0],
            [snapshot.frontier[3][0].0, snapshot.frontier[3][1].0, snapshot.frontier[3][2].0, snapshot.frontier[3][3].0, snapshot.frontier[3][4].0, snapshot.frontier[3][5].0, snapshot.frontier[3][6].0, snapshot.frontier[3][7].0],
            [snapshot.frontier[4][0].0, snapshot.frontier[4][1].0, snapshot.frontier[4][2].0, snapshot.frontier[4][3].0, snapshot.frontier[4][4].0, snapshot.frontier[4][5].0, snapshot.frontier[4][6].0, snapshot.frontier[4][7].0],
            [snapshot.frontier[5][0].0, snapshot.frontier[5][1].0, snapshot.frontier[5][2].0, snapshot.frontier[5][3].0, snapshot.frontier[5][4].0, snapshot.frontier[5][5].0, snapshot.frontier[5][6].0, snapshot.frontier[5][7].0],
            [snapshot.frontier[6][0].0, snapshot.frontier[6][1].0, snapshot.frontier[6][2].0, snapshot.frontier[6][3].0, snapshot.frontier[6][4].0, snapshot.frontier[6][5].0, snapshot.frontier[6][6].0, snapshot.frontier[6][7].0],
            [snapshot.frontier[7][0].0, snapshot.frontier[7][1].0, snapshot.frontier[7][2].0, snapshot.frontier[7][3].0, snapshot.frontier[7][4].0, snapshot.frontier[7][5].0, snapshot.frontier[7][6].0, snapshot.frontier[7][7].0],
            [snapshot.frontier[8][0].0, snapshot.frontier[8][1].0, snapshot.frontier[8][2].0, snapshot.frontier[8][3].0, snapshot.frontier[8][4].0, snapshot.frontier[8][5].0, snapshot.frontier[8][6].0, snapshot.frontier[8][7].0],
            [snapshot.frontier[9][0].0, snapshot.frontier[9][1].0, snapshot.frontier[9][2].0, snapshot.frontier[9][3].0, snapshot.frontier[9][4].0, snapshot.frontier[9][5].0, snapshot.frontier[9][6].0, snapshot.frontier[9][7].0],
            [snapshot.frontier[10][0].0, snapshot.frontier[10][1].0, snapshot.frontier[10][2].0, snapshot.frontier[10][3].0, snapshot.frontier[10][4].0, snapshot.frontier[10][5].0, snapshot.frontier[10][6].0, snapshot.frontier[10][7].0],
            [snapshot.frontier[11][0].0, snapshot.frontier[11][1].0, snapshot.frontier[11][2].0, snapshot.frontier[11][3].0, snapshot.frontier[11][4].0, snapshot.frontier[11][5].0, snapshot.frontier[11][6].0, snapshot.frontier[11][7].0],
            [snapshot.frontier[12][0].0, snapshot.frontier[12][1].0, snapshot.frontier[12][2].0, snapshot.frontier[12][3].0, snapshot.frontier[12][4].0, snapshot.frontier[12][5].0, snapshot.frontier[12][6].0, snapshot.frontier[12][7].0],
            [snapshot.frontier[13][0].0, snapshot.frontier[13][1].0, snapshot.frontier[13][2].0, snapshot.frontier[13][3].0, snapshot.frontier[13][4].0, snapshot.frontier[13][5].0, snapshot.frontier[13][6].0, snapshot.frontier[13][7].0],
            [snapshot.frontier[14][0].0, snapshot.frontier[14][1].0, snapshot.frontier[14][2].0, snapshot.frontier[14][3].0, snapshot.frontier[14][4].0, snapshot.frontier[14][5].0, snapshot.frontier[14][6].0, snapshot.frontier[14][7].0],
            [snapshot.frontier[15][0].0, snapshot.frontier[15][1].0, snapshot.frontier[15][2].0, snapshot.frontier[15][3].0, snapshot.frontier[15][4].0, snapshot.frontier[15][5].0, snapshot.frontier[15][6].0, snapshot.frontier[15][7].0],
            [snapshot.frontier[16][0].0, snapshot.frontier[16][1].0, snapshot.frontier[16][2].0, snapshot.frontier[16][3].0, snapshot.frontier[16][4].0, snapshot.frontier[16][5].0, snapshot.frontier[16][6].0, snapshot.frontier[16][7].0],
            [snapshot.frontier[17][0].0, snapshot.frontier[17][1].0, snapshot.frontier[17][2].0, snapshot.frontier[17][3].0, snapshot.frontier[17][4].0, snapshot.frontier[17][5].0, snapshot.frontier[17][6].0, snapshot.frontier[17][7].0],
            [snapshot.frontier[18][0].0, snapshot.frontier[18][1].0, snapshot.frontier[18][2].0, snapshot.frontier[18][3].0, snapshot.frontier[18][4].0, snapshot.frontier[18][5].0, snapshot.frontier[18][6].0, snapshot.frontier[18][7].0],
            [snapshot.frontier[19][0].0, snapshot.frontier[19][1].0, snapshot.frontier[19][2].0, snapshot.frontier[19][3].0, snapshot.frontier[19][4].0, snapshot.frontier[19][5].0, snapshot.frontier[19][6].0, snapshot.frontier[19][7].0],
        ],
        empty: [
            [empty[0][0].0, empty[0][1].0, empty[0][2].0, empty[0][3].0, empty[0][4].0, empty[0][5].0, empty[0][6].0, empty[0][7].0],
            [empty[1][0].0, empty[1][1].0, empty[1][2].0, empty[1][3].0, empty[1][4].0, empty[1][5].0, empty[1][6].0, empty[1][7].0],
            [empty[2][0].0, empty[2][1].0, empty[2][2].0, empty[2][3].0, empty[2][4].0, empty[2][5].0, empty[2][6].0, empty[2][7].0],
            [empty[3][0].0, empty[3][1].0, empty[3][2].0, empty[3][3].0, empty[3][4].0, empty[3][5].0, empty[3][6].0, empty[3][7].0],
            [empty[4][0].0, empty[4][1].0, empty[4][2].0, empty[4][3].0, empty[4][4].0, empty[4][5].0, empty[4][6].0, empty[4][7].0],
            [empty[5][0].0, empty[5][1].0, empty[5][2].0, empty[5][3].0, empty[5][4].0, empty[5][5].0, empty[5][6].0, empty[5][7].0],
            [empty[6][0].0, empty[6][1].0, empty[6][2].0, empty[6][3].0, empty[6][4].0, empty[6][5].0, empty[6][6].0, empty[6][7].0],
            [empty[7][0].0, empty[7][1].0, empty[7][2].0, empty[7][3].0, empty[7][4].0, empty[7][5].0, empty[7][6].0, empty[7][7].0],
            [empty[8][0].0, empty[8][1].0, empty[8][2].0, empty[8][3].0, empty[8][4].0, empty[8][5].0, empty[8][6].0, empty[8][7].0],
            [empty[9][0].0, empty[9][1].0, empty[9][2].0, empty[9][3].0, empty[9][4].0, empty[9][5].0, empty[9][6].0, empty[9][7].0],
            [empty[10][0].0, empty[10][1].0, empty[10][2].0, empty[10][3].0, empty[10][4].0, empty[10][5].0, empty[10][6].0, empty[10][7].0],
            [empty[11][0].0, empty[11][1].0, empty[11][2].0, empty[11][3].0, empty[11][4].0, empty[11][5].0, empty[11][6].0, empty[11][7].0],
            [empty[12][0].0, empty[12][1].0, empty[12][2].0, empty[12][3].0, empty[12][4].0, empty[12][5].0, empty[12][6].0, empty[12][7].0],
            [empty[13][0].0, empty[13][1].0, empty[13][2].0, empty[13][3].0, empty[13][4].0, empty[13][5].0, empty[13][6].0, empty[13][7].0],
            [empty[14][0].0, empty[14][1].0, empty[14][2].0, empty[14][3].0, empty[14][4].0, empty[14][5].0, empty[14][6].0, empty[14][7].0],
            [empty[15][0].0, empty[15][1].0, empty[15][2].0, empty[15][3].0, empty[15][4].0, empty[15][5].0, empty[15][6].0, empty[15][7].0],
            [empty[16][0].0, empty[16][1].0, empty[16][2].0, empty[16][3].0, empty[16][4].0, empty[16][5].0, empty[16][6].0, empty[16][7].0],
            [empty[17][0].0, empty[17][1].0, empty[17][2].0, empty[17][3].0, empty[17][4].0, empty[17][5].0, empty[17][6].0, empty[17][7].0],
            [empty[18][0].0, empty[18][1].0, empty[18][2].0, empty[18][3].0, empty[18][4].0, empty[18][5].0, empty[18][6].0, empty[18][7].0],
            [empty[19][0].0, empty[19][1].0, empty[19][2].0, empty[19][3].0, empty[19][4].0, empty[19][5].0, empty[19][6].0, empty[19][7].0],
        ],
    };
    (w, p)
}

// ---------- interface for the forest compiler ----------

fn digest(d: [u32; 8]) -> Digest {
    d.map(M31)
}

fn columns(flat: &[u32; cp::TRACE_CELLS]) -> [Vec<M31>; 16] {
    core::array::from_fn(|c| flat[c * 1024..(c + 1) * 1024].iter().map(|x| M31(*x)).collect())
}

/// The Lean `RustWitness` / `RustPublic` records of one compilation.
pub(super) struct CopyRecords {
    w: RW,
    p: RP,
}

/// The copy-built banks: `stable`, `late` and the merged semantic C1 trace.
pub(super) struct CopyBanks {
    pub(super) stable: [Vec<M31>; 16],
    pub(super) late: [Vec<M31>; 16],
    pub(super) merged: [Vec<M31>; 16],
}

impl CopyRecords {
    /// `recipient` is `Some` exactly for a private transfer; `out_value` is the
    /// recipient value or the withdrawal amount.
    pub(super) fn new(
        input: &PoolV1PairForestInputNoteWitnessV1,
        out_value: u32,
        recipient: Option<&PoolV1OutputNoteWitnessV1>,
        change: &PoolV1OutputNoteWitnessV1,
        snapshot: &PoolV1PairLiveSnapshotV1,
        asset: M31,
    ) -> Self {
        let (w, p) = records(input, out_value, recipient, change, snapshot, asset);
        Self { w, p }
    }

    /// Block 3: the input note commitment.
    pub(super) fn input_leaf(&self) -> Digest {
        digest(input_leaf_r(&self.w, &self.p))
    }

    /// The path digest after `levels` node blocks (`treeCurR`): 1 is the input
    /// pair leaf, 21 the lane root, 24 the global forest anchor.  Levels above
    /// 21 read the super-root siblings, which the caller must have checked
    /// canonical first.
    pub(super) fn path_digest(&self, levels: usize) -> Digest {
        digest(tree_cur_r(&self.w, &self.p, levels))
    }

    /// Block 26: the nullifier.
    pub(super) fn nullifier(&self) -> Digest {
        digest(note_digest_r(&self.w, &self.p, 26))
    }

    /// Block 29: the recipient commitment (transfer only).
    pub(super) fn recipient(&self) -> Digest {
        digest(recip_dr(&self.w, &self.p))
    }

    /// Block 32: the change commitment.
    pub(super) fn change(&self) -> Digest {
        digest(change_dr(&self.w, &self.p))
    }

    /// Block 33: the output pair.
    pub(super) fn output_pair(&self) -> Digest {
        digest(out_pair_r(&self.w, &self.p))
    }

    /// Block 53: the append root after the twenty live levels.
    pub(super) fn append_root(&self) -> Digest {
        digest(app_cur_r(&self.w, &self.p, 20))
    }

    /// The merged builder: `None` when the merge shape check fails.
    pub(super) fn banks(&self) -> Option<CopyBanks> {
        let (ok, stable, late, merged) = merged_banks(&self.w, &self.p);
        if !ok {
            return None;
        }
        Some(CopyBanks { stable: columns(&stable), late: columns(&late), merged: columns(&merged) })
    }
}

/// The extracted bank merge on production banks (each 16 columns of 1024
/// rows): `None` when `merge_check` fails, otherwise `merge_copy`.
pub(super) fn merge_banks(stable: &[Vec<M31>; 16], late: &[Vec<M31>; 16]) -> Option<[Vec<M31>; 16]> {
    let mut s = Box::new([0u32; cp::TRACE_CELLS]);
    let mut l = Box::new([0u32; cp::TRACE_CELLS]);
    for c in 0..16 {
        for r in 0..1024 {
            s[c * 1024 + r] = stable[c][r].0;
            l[c * 1024 + r] = late[c][r].0;
        }
    }
    if !cp::merge_check(&s, &l) {
        return None;
    }
    Some(columns(&cp::merge_copy(&s, &l)))
}

// Extraction-only equivalence harness; absent from normal prover/program builds.
#[cfg(kani)]
#[path = "../../../../tools/r1-builder-reference/records.rs"]
mod records_proofs;

// Owned reference only for bounded proof/extraction builds.
#[cfg(any(kani, aeneas_ref))]
#[path = "../../../../tools/r1-builder-reference/records_reference.rs"]
mod records_reference;
