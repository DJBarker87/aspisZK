//! Native differential tests: production writers (exported read-only from
//! origin/codex/100bit-spend-path-20261013, with the scratch-only shims of
//! shim.patch.txt) against the extraction-friendly copies in refine/writers.
use aspis_core::field::{M31, P};
use aspis_r0_writer_copies as cp;
use aspis_statement::{
    derive_owner_key,
    poseidon2::Digest,
    pool_v1::{
        pair_forest_trace::{
            compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
            compile_pool_v1_pair_forest_withdrawal_merged_c1_v1, diff_write_forest_path_aux,
            merge_pool_v1_pair_forest_trace_banks_v1, PoolV1PairForestInputNoteWitnessV1,
            PoolV1PairForestMergedC1CompilationV1, PoolV1PairForestPrivateTransferWitnessV1,
            PoolV1PairForestTraceV1, PoolV1PairForestWithdrawalWitnessV1,
        },
        pair_trace::{
            diff_write_occupancy, diff_write_value_aux, PoolV1PairInputNoteWitnessV1,
        },
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

fn empty_columns() -> [Vec<M31>; 16] {
    core::array::from_fn(|_| vec![M31(0); 1024])
}

fn raw(d: &Digest) -> [u32; 8] {
    core::array::from_fn(|i| d[i].0)
}

/// Compare a copy block (row-major, 16 columns) with production columns at rows start..
fn same_block(cols: &[Vec<M31>; 16], start: usize, block: &[u32], rows: usize) -> bool {
    for r in 0..rows {
        for c in 0..16 {
            if cols[c][start + r].0 != block[r * 16 + c] {
                return false;
            }
        }
    }
    true
}

fn occ_record(w: &PoolV1PairLeafWitnessV1, selected: Option<bool>) -> cp::OccRecord {
    cp::OccRecord {
        occupied: w.second_occupied.0,
        inverse: w.second_occupancy_inverse.0,
        commitment: raw(&w.second_commitment),
        selected: selected.map(u32::from).unwrap_or(0),
        has_selected: selected.is_some(),
    }
}

#[test]
fn value_writer_matches() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let edge = [0u32, 1, (1 << 30) - 1, 1 << 29, 12345];
    let mut n = 0u64;
    for i in 0..200_000u64 {
        let values: [u32; 3] = if i < 125 {
            [edge[(i % 5) as usize], edge[((i / 5) % 5) as usize], edge[((i / 25) % 5) as usize]]
        } else {
            core::array::from_fn(|_| rng.below(1 << 30) as u32)
        };
        let mut cols = empty_columns();
        diff_write_value_aux(&mut cols, values);
        // the legacy value block (rows 960..975) is relocated verbatim to 1008..1023
        let block = cp::write_value_block(values);
        assert!(same_block(&cols, 960, &block, 16), "values {values:?}");
        n += 1;
    }
    println!("value_writer_matches: {n} cases");
}

#[test]
fn occupancy_writer_matches() {
    let mut rng = Rng(0x1234_5678_9abc_def1);
    let mut n = 0u64;
    for _ in 0..100_000u64 {
        let leaf = PoolV1PairLeafWitnessV1 {
            first_commitment: rng.digest(),
            second_occupied: M31(rng.m31()),
            second_commitment: rng.digest(),
            second_occupancy_inverse: M31(rng.m31()),
        };
        let sel = match rng.below(3) {
            0 => None,
            1 => Some(false),
            _ => Some(true),
        };
        let local = 9 + rng.below(2) as usize;
        let mut cols = empty_columns();
        diff_write_occupancy(&mut cols, 960 + local, leaf, sel);
        let block = cp::write_occupancy_row([0u32; cp::AUX_BLOCK_CELLS], local, occ_record(&leaf, sel));
        assert!(same_block(&cols, 960, &block, 16));
        n += 1;
    }
    println!("occupancy_writer_matches: {n} cases");
}

#[test]
fn path_writer_matches() {
    let mut rng = Rng(0x0f0e_0d0c_0b0a_0908);
    let mut n = 0u64;
    for _ in 0..50_000u64 {
        let level = rng.below(24) as usize;
        let bit = rng.below(2) as u32;
        let (cur, l, r) = (rng.digest(), rng.digest(), rng.digest());
        let mut cols = empty_columns();
        diff_write_forest_path_aux(&mut cols, level, M31(bit), cur, l, r).unwrap();
        let buf = cp::write_path_level([0u32; cp::PATH_BLOCK_CELLS], level, bit, raw(&cur), raw(&l), raw(&r));
        assert!(same_block(&cols, 912, &buf, 96));
        n += 1;
    }
    for _ in 0..2_000u64 {
        let bits: [u32; 24] = core::array::from_fn(|_| rng.below(2) as u32);
        let cur: [Digest; 24] = core::array::from_fn(|_| rng.digest());
        let l: [Digest; 24] = core::array::from_fn(|_| rng.digest());
        let r: [Digest; 24] = core::array::from_fn(|_| rng.digest());
        let mut cols = empty_columns();
        for level in 0..24 {
            diff_write_forest_path_aux(&mut cols, level, M31(bits[level]), cur[level], l[level], r[level]).unwrap();
        }
        let buf = cp::write_path_block(bits, core::array::from_fn(|i| raw(&cur[i])),
            core::array::from_fn(|i| raw(&l[i])), core::array::from_fn(|i| raw(&r[i])));
        assert!(same_block(&cols, 912, &buf, 96));
        n += 1;
    }
    println!("path_writer_matches: {n} cases");
}

#[test]
fn node_right_lane7_matches() {
    let mut rng = Rng(0x5555_aaaa_3333_cccc);
    for i in 0..1_000_000u64 {
        let x = if i < 4 { [0, 1, P - 1, cp::TWEAK][i as usize] } else { rng.m31() };
        assert_eq!(M31(x).sub(M31(cp::TWEAK)).0, cp::node_right_lane7(x));
    }
    println!("node_right_lane7_matches: 1000000 cases");
}

fn flat(cols: &[Vec<M31>; 16]) -> Box<[u32; cp::TRACE_CELLS]> {
    let mut out = Box::new([0u32; cp::TRACE_CELLS]);
    for c in 0..16 {
        for r in 0..1024 {
            out[c * 1024 + r] = cols[c][r].0;
        }
    }
    out
}

fn check_merge(trace: &PoolV1PairForestTraceV1) -> bool {
    let stable = flat(&trace.stable.c1);
    let late = flat(&trace.late);
    let prod = merge_pool_v1_pair_forest_trace_banks_v1(trace);
    let ok = cp::merge_check(&stable, &late);
    match prod {
        Ok(merged) => ok && cp::merge_copy(&stable, &late) == *flat(&merged.c1),
        Err(_) => !ok,
    }
}

// ---------- fixture-level: the full honest compile ----------

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

/// Independent path data: (bit, current, left, right) per level, from the
/// witness and pool_v1_tree_parent only.
fn path_data(input: &PoolV1PairForestInputNoteWitnessV1, leaf: Digest) -> ([u32; 24], [[u32; 8]; 24], [[u32; 8]; 24], [[u32; 8]; 24]) {
    let mut bits = [0u32; 24];
    let mut cur = [[0u32; 8]; 24];
    let mut left = [[0u32; 8]; 24];
    let mut right = [[0u32; 8]; 24];
    let pair = &input.pair;
    let other = if pair.selected_second { pair.pair_leaf.first_commitment } else { pair.pair_leaf.second_commitment };
    let mut current = leaf;
    for level in 0..24 {
        let (bit, sib) = if level == 0 {
            (u32::from(pair.selected_second), other)
        } else if level <= 20 {
            (((pair.membership.index >> (level - 1)) & 1) as u32, pair.membership.siblings[level - 1])
        } else {
            (u32::from(input.super_root_directions[level - 21]), input.super_root_siblings[level - 21])
        };
        let (l, r) = if bit == 0 { (current, sib) } else { (sib, current) };
        bits[level] = bit;
        cur[level] = raw(&current);
        left[level] = raw(&l);
        right[level] = raw(&r);
        current = pool_v1_tree_parent(&l, &r);
    }
    (bits, cur, left, right)
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

fn check_compiled(
    comp: &PoolV1PairForestMergedC1CompilationV1,
    input: &PoolV1PairForestInputNoteWitnessV1,
    values: [u32; 3],
    output_leaf: PoolV1PairLeafWitnessV1,
) {
    let c1 = &comp.semantic_c1.c1;
    let pair = &input.pair;
    let input_occ = occ_record(&pair.pair_leaf, Some(pair.selected_second));
    let output_occ = occ_record(&output_leaf, None);
    let aux = cp::write_aux_block(values, input_occ, output_occ);
    assert!(same_block(c1, 1008, &aux, 16), "aux block");
    let leaf = *pair.pair_leaf.selected_commitment(pair.selected_second);
    let (bits, cur, l, r) = path_data(input, leaf);
    let path = cp::write_path_block(bits, cur, l, r);
    assert!(same_block(c1, 912, &path, 96), "path block");
    assert!(check_merge(&comp.trace), "merge");
}

fn run_transfer(rng: Option<&mut Rng>, input_value: u32, rec_value: u32) {
    let mut local = Rng(1);
    let (rng, randomized) = match rng { Some(r) => (r, true), None => (&mut local, false) };
    let input = if randomized { input_witness(input_value, Some(rng)) } else { input_witness(input_value, None) };
    let (rec, chg) = if randomized {
        (PoolV1OutputNoteWitnessV1 { owner_key: rng.digest(), salt: rng.digest(), value: rec_value },
         PoolV1OutputNoteWitnessV1 { owner_key: rng.digest(), salt: rng.digest(), value: input_value - rec_value })
    } else {
        (PoolV1OutputNoteWitnessV1 { owner_key: digest_seed(300), salt: digest_seed(400), value: 600 },
         PoolV1OutputNoteWitnessV1 { owner_key: digest_seed(500), salt: digest_seed(600), value: 400 })
    };
    let asset = M31(77);
    let anchor = global_anchor(&input);
    let rc = pool_v1_note_commitment(&rec.owner_key, rec.value, asset, &rec.salt);
    let cc = pool_v1_note_commitment(&chg.owner_key, chg.value, asset, &chg.salt);
    let public = PoolV1PrivateTransferPublicV1 {
        pool: [1; 32],
        deployment_domain: [2; 32],
        anchor_sequence: 42,
        anchor_root: anchor,
        nullifier: pool_v1_nullifier(&input.pair.nullifier_key, &input.pair.salt),
        asset_id: asset,
        recipient_commitment: rc,
        change_commitment: cc,
    };
    let output_leaf = match PoolV1PairLeafWitnessV1::two_outputs(rc, cc) {
        Ok(l) => l,
        Err(_) => return, // zero change sentinel: the builder's salt retry (D50)
    };
    let witness = PoolV1PairForestPrivateTransferWitnessV1 { input, recipient: rec, change: chg };
    let comp = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
        &public, &witness, context(public.pool, public.deployment_domain, anchor, asset),
        snapshot_at(public.pool, public.deployment_domain, 13)).unwrap();
    check_compiled(&comp, &input, [input.pair.value, rec.value, chg.value], output_leaf);
}

fn run_withdrawal(rng: Option<&mut Rng>, input_value: u32, amount: u32) {
    let mut local = Rng(1);
    let (rng, randomized) = match rng { Some(r) => (r, true), None => (&mut local, false) };
    let input = if randomized { input_witness(input_value, Some(rng)) } else { input_witness(input_value, None) };
    let chg = if randomized {
        PoolV1OutputNoteWitnessV1 { owner_key: rng.digest(), salt: rng.digest(), value: input_value - amount }
    } else {
        PoolV1OutputNoteWitnessV1 { owner_key: digest_seed(700), salt: digest_seed(800), value: 750 }
    };
    let asset = M31(77);
    let anchor = global_anchor(&input);
    let cc = pool_v1_note_commitment(&chg.owner_key, chg.value, asset, &chg.salt);
    let public = PoolV1WithdrawalPublicV1 {
        pool: [1; 32],
        deployment_domain: [2; 32],
        anchor_sequence: 42,
        anchor_root: anchor,
        nullifier: pool_v1_nullifier(&input.pair.nullifier_key, &input.pair.salt),
        asset_id: asset,
        amount,
        destination_token_account: [9; 32],
        change_commitment: cc,
    };
    let witness = PoolV1PairForestWithdrawalWitnessV1 { input, change: chg };
    let comp = compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(
        &public, &witness, context(public.pool, public.deployment_domain, anchor, asset),
        snapshot_at(public.pool, public.deployment_domain, 13)).unwrap();
    check_compiled(&comp, &input, [input.pair.value, amount, chg.value],
        PoolV1PairLeafWitnessV1::single_output(cc).unwrap());
}

#[test]
fn fixtures_match() {
    run_transfer(None, 1_000, 600);
    run_withdrawal(None, 1_000, 250);
    println!("fixtures_match: saved transfer and withdrawal fixtures");
}

#[test]
fn randomized_witnesses_match() {
    let mut rng = Rng(0xdead_beef_0bad_f00d);
    let mut n = 0;
    for i in 0..256u64 {
        let input_value = 2 + rng.below((1 << 30) - 2) as u32;
        let part = 1 + rng.below(input_value as u64 - 1) as u32;
        if i % 2 == 0 {
            run_transfer(Some(&mut rng), input_value, part);
        } else {
            run_withdrawal(Some(&mut rng), input_value, part);
        }
        n += 1;
    }
    println!("randomized_witnesses_match: {n} witnesses");
}

#[test]
fn merge_matches_random_banks() {
    let mut rng = Rng(0x7777_1111_2222_3333);
    let fixture = {
        let input = input_witness(1_000, None);
        let asset = M31(77);
        let anchor = global_anchor(&input);
        let chg = PoolV1OutputNoteWitnessV1 { owner_key: digest_seed(700), salt: digest_seed(800), value: 750 };
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1; 32], deployment_domain: [2; 32], anchor_sequence: 42, anchor_root: anchor,
            nullifier: pool_v1_nullifier(&input.pair.nullifier_key, &input.pair.salt), asset_id: asset,
            amount: 250, destination_token_account: [9; 32],
            change_commitment: pool_v1_note_commitment(&chg.owner_key, chg.value, asset, &chg.salt),
        };
        compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(&public,
            &PoolV1PairForestWithdrawalWitnessV1 { input, change: chg },
            context(public.pool, public.deployment_domain, anchor, asset),
            snapshot_at(public.pool, public.deployment_domain, 13)).unwrap().trace
    };
    let mut n = 0;
    for _ in 0..2_000u64 {
        let mut t = fixture.clone();
        for c in 0..16 {
            for r in 0..1024 {
                let late_row = (544..864).contains(&r);
                t.stable.c1[c][r] = M31(if late_row { 0 } else { rng.m31() });
                t.late[c][r] = M31(if late_row { rng.m31() } else { 0 });
            }
        }
        // inject 0, 1 or 2 shape violations
        for _ in 0..rng.below(3) {
            let c = rng.below(16) as usize;
            let r = rng.below(1024) as usize;
            if (544..864).contains(&r) { t.stable.c1[c][r] = M31(1 + rng.below(P as u64 - 1) as u32); }
            else { t.late[c][r] = M31(1 + rng.below(P as u64 - 1) as u32); }
        }
        assert!(check_merge(&t));
        n += 1;
    }
    println!("merge_matches_random_banks: {n} cases");
}

/// Every one of the 57 Poseidon blocks of real compiled traces has the
/// abstract-permutation layout of refine/blockwriters::write_block, with the
/// rounds produced by the production permutation on row 0 + row 12.
#[test]
fn compiled_blocks_have_block_layout() {
    use aspis_r0_block_writer_copies as bw;
    use aspis_statement::poseidon2::permute_optimized_with_trace;
    let mut rng = Rng(0x0bad_cafe_dead_beef);
    let mut n = 0;
    for i in 0..64u64 {
        let input_value = 2 + rng.below((1 << 30) - 2) as u32;
        let part = 1 + rng.below(input_value as u64 - 1) as u32;
        let comp = if i == 0 {
            None
        } else {
            Some((input_value, part, i % 2 == 0))
        };
        let c1 = compiled_c1(comp, &mut rng);
        for block in 0..57 {
            let pre: [u32; 16] = core::array::from_fn(|c| c1[c][block * 16].0);
            let abs: [u32; 16] = core::array::from_fn(|c| c1[c][block * 16 + 12].0);
            let mut state: [M31; 16] = core::array::from_fn(|c| M31(pre[c]).add(M31(abs[c])));
            let mut rounds = [[0u32; 16]; 11];
            permute_optimized_with_trace(&mut state, |t| {
                if t.round & 1 == 1 {
                    rounds[usize::from(t.round) / 2] = core::array::from_fn(|c| t.output[c].0);
                }
            });
            let cells = bw::write_block(&pre, &abs, &rounds);
            assert!(same_block(&c1, block * 16, &cells, 16), "block {block}");
            n += 1;
        }
    }
    println!("compiled_blocks_have_block_layout: {n} blocks");
}

fn compiled_c1(spec: Option<(u32, u32, bool)>, rng: &mut Rng) -> [Vec<M31>; 16] {
    let input = match spec { None => input_witness(1_000, None), Some((v, _, _)) => input_witness(v, Some(&mut *rng)) };
    let asset = M31(77);
    let anchor = global_anchor(&input);
    let snapshot = snapshot_at([1; 32], [2; 32], 13);
    let (value, part, transfer) = spec.unwrap_or((1_000, 600, true));
    let chg = PoolV1OutputNoteWitnessV1 { owner_key: rng.digest(), salt: rng.digest(), value: value - part };
    let nullifier = pool_v1_nullifier(&input.pair.nullifier_key, &input.pair.salt);
    let cc = pool_v1_note_commitment(&chg.owner_key, chg.value, asset, &chg.salt);
    if transfer {
        let rec = PoolV1OutputNoteWitnessV1 { owner_key: rng.digest(), salt: rng.digest(), value: part };
        let rc = pool_v1_note_commitment(&rec.owner_key, rec.value, asset, &rec.salt);
        let public = PoolV1PrivateTransferPublicV1 {
            pool: [1; 32], deployment_domain: [2; 32], anchor_sequence: 42, anchor_root: anchor,
            nullifier, asset_id: asset, recipient_commitment: rc, change_commitment: cc,
        };
        match compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&public,
            &PoolV1PairForestPrivateTransferWitnessV1 { input, recipient: rec, change: chg },
            context(public.pool, public.deployment_domain, anchor, asset), snapshot) {
            Ok(c) => c.semantic_c1.c1.clone(),
            Err(_) => compiled_c1(None, rng), // zero change sentinel: salt retry (D50)
        }
    } else {
        let public = PoolV1WithdrawalPublicV1 {
            pool: [1; 32], deployment_domain: [2; 32], anchor_sequence: 42, anchor_root: anchor,
            nullifier, asset_id: asset, amount: part, destination_token_account: [9; 32],
            change_commitment: cc,
        };
        compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(&public,
            &PoolV1PairForestWithdrawalWitnessV1 { input, change: chg },
            context(public.pool, public.deployment_domain, anchor, asset), snapshot).unwrap().semantic_c1.c1.clone()
    }
}

/// The Poseidon copy reproduces rows 1..11 of every block of real traces.
#[test]
fn compiled_blocks_rounds_match_copy() {
    let mut rng = Rng(0x5eed_5eed_5eed_5eed);
    let mut n = 0;
    for i in 0..32u64 {
        let input_value = 2 + rng.below((1 << 30) - 2) as u32;
        let part = 1 + rng.below(input_value as u64 - 1) as u32;
        let c1 = compiled_c1(Some((input_value, part, i % 2 == 0)), &mut rng);
        for block in 0..57 {
            let pre: [u32; 16] = core::array::from_fn(|c| c1[c][block * 16].0);
            let abs: [u32; 16] = core::array::from_fn(|c| c1[c][block * 16 + 12].0);
            let rounds = aspis_r0_poseidon_copy::perm_rounds(&pre, &abs);
            for r in 0..11 {
                for c in 0..16 {
                    assert_eq!(c1[c][block * 16 + r + 1].0, rounds[r][c], "block {block} row {}", r + 1);
                }
            }
            n += 1;
        }
    }
    println!("compiled_blocks_rounds_match_copy: {n} blocks");
}
