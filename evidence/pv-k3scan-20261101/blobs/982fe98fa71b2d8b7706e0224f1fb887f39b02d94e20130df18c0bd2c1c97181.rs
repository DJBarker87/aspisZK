//! Native differential test of the Lean glue (DESIGN-BUILDER-MODEL §13 (1)).
//!
//! `copy_cell_merged` mirrors R0Z `copyCellMerged` (BuilderWitnessMerged.lean)
//! over the extracted copies (refine/blockwriters, refine/poseidon,
//! refine/writers).  The table-driven glue (sponge schedule, chunks, child
//! dispatch, row ranges) is `include!`d from glue_gen.rs, generated from the
//! same table whose Lean rendering gen-glue.py.txt --check finds verbatim in
//! the proved Lean files; the structural glue below is one Rust function per
//! Lean definition (same name, snake case).  The full 16 x 1024 C1 trace is
//! compared with the production forest compile on the saved fixtures and on
//! randomized honest witnesses; columns 16..28 are zero in the copy (the model
//! fixes the stage-H columns to 0).
use aspis_core::field::{M31, P};
use aspis_r0_block_writer_copies as bw;
use aspis_r0_writer_copies as cp;
use aspis_statement::{
    derive_owner_key,
    poseidon2::Digest,
    pool_v1::{
        pair_forest_trace::{
            compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
            compile_pool_v1_pair_forest_withdrawal_merged_c1_v1, PoolV1PairForestInputNoteWitnessV1,
            PoolV1PairForestPrivateTransferWitnessV1, PoolV1PairForestWithdrawalWitnessV1,
        },
        pair_trace::PoolV1PairInputNoteWitnessV1,
        pool_v1_note_commitment, pool_v1_nullifier, pool_v1_tree_parent, IncrementalMerkleTreeV1,
        PoolV1MembershipWitnessV1, PoolV1OutputNoteWitnessV1, PoolV1PairLeafWitnessV1,
        PoolV1PairLiveSnapshotV1, PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
        PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1, POOL_V1_PAIR_TREE_DEPTH,
    },
};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn m31(&mut self) -> u32 {
        self.below(P as u64) as u32
    }
    fn digest(&mut self) -> Digest {
        core::array::from_fn(|_| M31(self.m31()))
    }
}

fn raw(d: &Digest) -> [u32; 8] {
    core::array::from_fn(|i| d[i].0)
}

fn context<'a>(pool: [u8; 32], dom: [u8; 32], anchor: Digest, asset: M31) -> PoolV1PaymentRelationContextV1<'a> {
    PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            pool,
            deployment_domain: dom,
            anchor_sequence: 42,
            anchor_root: anchor,
            asset_id: asset,
        },
        spent_nullifiers: &[],
    }
}

fn digest_seed(seed: u32) -> Digest {
    core::array::from_fn(|lane| M31(seed + 17 * lane as u32 + 1))
}

fn pair_empty_roots() -> [Digest; POOL_V1_PAIR_TREE_DEPTH + 1] {
    let zero = [M31(0); 8];
    let mut roots = [zero; POOL_V1_PAIR_TREE_DEPTH + 1];
    roots[0] = pool_v1_tree_parent(&zero, &zero);
    for level in 0..POOL_V1_PAIR_TREE_DEPTH {
        roots[level + 1] = pool_v1_tree_parent(&roots[level], &roots[level]);
    }
    roots
}

fn snapshot_at(pool: [u8; 32], dom: [u8; 32], index: u64) -> PoolV1PairLiveSnapshotV1 {
    let empty = pair_empty_roots();
    let mut tree = IncrementalMerkleTreeV1::from_parts_with_empty_roots(
        0, empty[POOL_V1_PAIR_TREE_DEPTH], core::array::from_fn(|level| empty[level]), &empty).unwrap();
    for leaf in 0..index {
        tree = tree.append_one_with_empty_roots(digest_seed(20_000 + 32 * leaf as u32), &empty).unwrap().0;
    }
    PoolV1PairLiveSnapshotV1 {
        pool,
        deployment_domain: dom,
        sequence: index,
        next_pair_index: index,
        current_root: tree.root,
        frontier: tree.frontier,
    }
}

/// The saved fixture (pool_v1_pair_forest_honest.rs tests) when `rng` is None,
/// otherwise a randomized witness of the same shape.
fn input_witness(value: u32, rng: Option<&mut Rng>) -> PoolV1PairForestInputNoteWitnessV1 {
    let asset = M31(77);
    match rng {
        None => {
            let nullifier_key = digest_seed(10);
            let salt = digest_seed(100);
            let owner = derive_owner_key(&nullifier_key);
            let c = pool_v1_note_commitment(&owner, value, asset, &salt);
            PoolV1PairForestInputNoteWitnessV1 {
                pair: PoolV1PairInputNoteWitnessV1 {
                    nullifier_key,
                    salt,
                    value,
                    pair_leaf: PoolV1PairLeafWitnessV1::two_outputs(c, digest_seed(900)).unwrap(),
                    selected_second: false,
                    membership: PoolV1MembershipWitnessV1 {
                        siblings: core::array::from_fn(|level| digest_seed(2_000 + 20 * level as u32)),
                        index: 0x5_4321,
                    },
                },
                super_root_siblings: [digest_seed(3_000), digest_seed(3_100), digest_seed(3_200)],
                super_root_directions: [true, false, true],
            }
        }
        Some(rng) => {
            let nullifier_key = rng.digest();
            let salt = rng.digest();
            let owner = derive_owner_key(&nullifier_key);
            let c = pool_v1_note_commitment(&owner, value, asset, &salt);
            let mut other = rng.digest();
            if other[7].0 == 0 {
                other[7] = M31(1);
            }
            let selected_second = rng.below(2) == 1;
            let pair_leaf = if selected_second {
                PoolV1PairLeafWitnessV1::two_outputs(other, c).unwrap()
            } else if rng.below(2) == 1 {
                PoolV1PairLeafWitnessV1::two_outputs(c, other).unwrap()
            } else {
                PoolV1PairLeafWitnessV1::single_output(c).unwrap()
            };
            PoolV1PairForestInputNoteWitnessV1 {
                pair: PoolV1PairInputNoteWitnessV1 {
                    nullifier_key,
                    salt,
                    value,
                    pair_leaf,
                    selected_second,
                    membership: PoolV1MembershipWitnessV1 {
                        siblings: core::array::from_fn(|_| rng.digest()),
                        index: rng.below(1 << 20) as u32,
                    },
                },
                super_root_siblings: [rng.digest(), rng.digest(), rng.digest()],
                super_root_directions: core::array::from_fn(|_| rng.below(2) == 1),
            }
        }
    }
}

fn global_anchor(input: &PoolV1PairForestInputNoteWitnessV1) -> Digest {
    let mut current = input.pair.pair_leaf.leaf_digest().unwrap();
    for level in 0..POOL_V1_PAIR_TREE_DEPTH {
        let s = input.pair.membership.siblings[level];
        current = if ((input.pair.membership.index >> level) & 1) == 0 {
            pool_v1_tree_parent(&current, &s)
        } else {
            pool_v1_tree_parent(&s, &current)
        };
    }
    for level in 0..3 {
        let s = input.super_root_siblings[level];
        current = if input.super_root_directions[level] {
            pool_v1_tree_parent(&s, &current)
        } else {
            pool_v1_tree_parent(&current, &s)
        };
    }
    current
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
/// stableBank / lateBank / mergedR / copyCellMerged
fn merged_trace(w: &RW, p: &RP) -> (bool, Vec<[u32; 1024]>) {
    let pt = parts(w, p);
    let mut stable = Box::new([0u32; cp::TRACE_CELLS]);
    let mut late = Box::new([0u32; cp::TRACE_CELLS]);
    for k in 0..cp::TRACE_CELLS {
        stable[k] = if late_row(k) { 0 } else { copy_cell(&pt, k / 1024, k % 1024) };
        late[k] = if late_row(k) { pt.blocks[k % 1024 / 16][(k % 1024 % 16) * 16 + k / 1024] } else { 0 };
    }
    let ok = cp::merge_check(&stable, &late);
    let merged = cp::merge_copy(&stable, &late);
    let cols = (0..29).map(|c| core::array::from_fn(|r| if c < C1_COLS { merged[c * 1024 + r] } else { 0 })).collect();
    (ok, cols)
}

include!("glue_gen.rs");

// ---------- the Wspend⁺ → record map on the Rust side ----------

fn records(input: &PoolV1PairForestInputNoteWitnessV1, out: u32, rec: Option<&PoolV1OutputNoteWitnessV1>,
           chg: &PoolV1OutputNoteWitnessV1, snapshot: &PoolV1PairLiveSnapshotV1) -> (RW, RP) {
    let pair = &input.pair;
    let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
    let mut bits = [0u32; 24];
    let mut sibs = [[0u32; 8]; 24];
    for level in 0..24 {
        let (bit, sib) = if level == 0 {
            (u32::from(pair.selected_second), other)
        } else if level <= 20 {
            (((pair.membership.index >> (level - 1)) & 1) as u32, pair.membership.siblings[level - 1])
        } else {
            (u32::from(input.super_root_directions[level - 21]), input.super_root_siblings[level - 21])
        };
        bits[level] = bit;
        sibs[level] = raw(&sib);
    }
    let empty = pair_empty_roots();
    let w = RW {
        input_value: pair.value,
        output_value: out,
        change_value: chg.value,
        sk: raw(&pair.nullifier_key),
        salt: raw(&pair.salt),
        bits,
        sibs,
        pair_first: raw(&pair.pair_leaf.first_commitment),
        pair_occupied: pair.pair_leaf.second_occupied.0,
        pair_second: raw(&pair.pair_leaf.second_commitment),
        pair_inverse: pair.pair_leaf.second_occupancy_inverse.0,
        recipient_owner: rec.map(|r| raw(&r.owner_key)).unwrap_or(ZERO8),
        recipient_salt: rec.map(|r| raw(&r.salt)).unwrap_or(ZERO8),
        change_owner: raw(&chg.owner_key),
        change_salt: raw(&chg.salt),
    };
    let p = RP {
        transfer: rec.is_some(),
        asset: 77,
        next_pair_index: snapshot.next_pair_index,
        frontier: core::array::from_fn(|l| raw(&snapshot.frontier[l])),
        empty: core::array::from_fn(|l| raw(&empty[l])),
    };
    (w, p)
}

fn compare(c1: &[Vec<M31>; 16], w: &RW, p: &RP) -> usize {
    let (ok, cols) = merged_trace(w, p);
    assert!(ok, "merge_check");
    let mut cells = 0;
    for c in 0..29 {
        for r in 0..1024 {
            if c < 16 {
                assert_eq!(cols[c][r], c1[c][r].0, "cell column {c} row {r}");
            } else {
                assert_eq!(cols[c][r], 0);
            }
            cells += 1;
        }
    }
    cells
}

/// One honest witness: Some(rng) randomized, None the saved fixture.  Returns
/// false when the production builder rejects it (zero change sentinel).
fn build(mut rng: Option<&mut Rng>, transfer: bool) -> Option<([Vec<M31>; 16], RW, RP)> {
    let randomized = rng.is_some();
    let (input_value, part, index) = match rng.as_deref_mut() {
        Some(r) => {
            let v = 2 + r.below((1 << 30) - 2) as u32;
            (v, 1 + r.below(v as u64 - 1) as u32, r.below(64))
        }
        None => (1_000, if transfer { 600 } else { 250 }, 13),
    };
    let input = match rng.as_deref_mut() { Some(r) => input_witness(input_value, Some(r)), None => input_witness(input_value, None) };
    let asset = M31(77);
    let anchor = global_anchor(&input);
    let snapshot = snapshot_at([1; 32], [2; 32], index);
    let nullifier = pool_v1_nullifier(&input.pair.nullifier_key, &input.pair.salt);
    let mut fresh = || -> Digest { match rng.as_deref_mut() { Some(r) => r.digest(), None => unreachable!() } };
    if transfer {
        let (rec, chg) = if randomized {
            (PoolV1OutputNoteWitnessV1 { owner_key: fresh(), salt: fresh(), value: part },
             PoolV1OutputNoteWitnessV1 { owner_key: fresh(), salt: fresh(), value: input_value - part })
        } else {
            (PoolV1OutputNoteWitnessV1 { owner_key: digest_seed(300), salt: digest_seed(400), value: 600 },
             PoolV1OutputNoteWitnessV1 { owner_key: digest_seed(500), salt: digest_seed(600), value: 400 })
        };
        let rc = pool_v1_note_commitment(&rec.owner_key, rec.value, asset, &rec.salt);
        let cc = pool_v1_note_commitment(&chg.owner_key, chg.value, asset, &chg.salt);
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32], deployment_domain: [2; 32], anchor_sequence: 42, anchor_root: anchor,
            nullifier, asset_id: asset, recipient_commitment: rc, change_commitment: cc,
        };
        let witness = PoolV1PairForestPrivateTransferWitnessV1 { input: input.clone(), recipient: rec.clone(), change: chg.clone() };
        let comp = match compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&public, &witness,
            context(public.pool, public.deployment_domain, anchor, asset), snapshot.clone()) {
            Ok(c) => c,
            Err(_) => return None,
        };
        let (w, p) = records(&input, rec.value, Some(&rec), &chg, &snapshot);
        Some((comp.semantic_c1.c1.clone(), w, p))
    } else {
        let chg = if randomized {
            PoolV1OutputNoteWitnessV1 { owner_key: fresh(), salt: fresh(), value: input_value - part }
        } else {
            PoolV1OutputNoteWitnessV1 { owner_key: digest_seed(700), salt: digest_seed(800), value: 750 }
        };
        let cc = pool_v1_note_commitment(&chg.owner_key, chg.value, asset, &chg.salt);
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1; 32], deployment_domain: [2; 32], anchor_sequence: 42, anchor_root: anchor,
            nullifier, asset_id: asset, amount: part, destination_token_account: [9; 32], change_commitment: cc,
        };
        let witness = PoolV1PairForestWithdrawalWitnessV1 { input: input.clone(), change: chg.clone() };
        let comp = compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(&public, &witness,
            context(public.pool, public.deployment_domain, anchor, asset), snapshot.clone()).unwrap();
        let (w, p) = records(&input, part, None, &chg, &snapshot);
        Some((comp.semantic_c1.c1.clone(), w, p))
    }
}

fn run(rng: Option<&mut Rng>, transfer: bool) -> bool {
    match build(rng, transfer) {
        Some((c1, w, p)) => { compare(&c1, &w, &p); true }
        None => false,
    }
}

fn mismatches(c1: &[Vec<M31>; 16], w: &RW, p: &RP) -> usize {
    let (_, cols) = merged_trace(w, p);
    (0..16).map(|c| (0..1024).filter(|&r| cols[c][r] != c1[c][r].0).count()).sum()
}

#[test]
fn glue_fixtures_match_production() {
    assert!(run(None, true));
    assert!(run(None, false));
    println!("glue_fixtures_match_production: saved transfer and withdrawal fixtures, 2 x 29 x 1024 cells");
}

#[test]
fn glue_randomized_match_production() {
    let mut rng = Rng(0x61_7573_7069_7331);
    let (mut ok, mut skipped, mut i) = (0u32, 0u32, 0u64);
    while ok < 512 {
        if run(Some(&mut rng), i % 2 == 0) { ok += 1 } else { skipped += 1 }
        i += 1;
    }
    println!("glue_randomized_match_production: {ok} witnesses ({} transfers / withdrawals alternating), {skipped} rejected by production (zero change sentinel), 29 x 1024 cells each", ok);
}

/// Teeth: one-entry mutations of the records fed to the mirrored glue are
/// detected against the production trace (each touches a different glue part).
#[test]
fn glue_mutations_caught() {
    let (c1, w, p) = build(None, true).unwrap();
    assert_eq!(mismatches(&c1, &w, &p), 0);
    let mut muts: Vec<(&str, RW, RP)> = Vec::new();
    let mut m = w.clone(); m.bits[5] ^= 1; muts.push(("membership bit", m, p.clone()));
    let mut m = w.clone(); m.bits[22] ^= 1; muts.push(("super-root bit", m, p.clone()));
    let mut q = p.clone(); q.next_pair_index ^= 1; muts.push(("append parity", w.clone(), q));
    let mut q = p.clone(); q.asset ^= 1; muts.push(("asset word", w.clone(), q));
    let mut m = w.clone(); m.change_salt[7] ^= 1; muts.push(("change salt lane 7", m, p.clone()));
    let mut m = w.clone(); m.pair_inverse ^= 1; muts.push(("pair inverse", m, p.clone()));
    let mut q = p.clone(); q.transfer = false; muts.push(("variant", w.clone(), q));
    for (name, mw, mp) in &muts {
        let n = mismatches(&c1, mw, mp);
        assert!(n > 0, "mutation {name} not detected");
        println!("  mutation {name}: {n} cells differ");
    }
    println!("glue_mutations_caught: {} mutations detected", muts.len());
}
