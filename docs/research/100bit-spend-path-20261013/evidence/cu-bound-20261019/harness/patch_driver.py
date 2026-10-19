#!/usr/bin/env python3
"""Derive the CU-bound sweep driver from the exact pool_gate.rs used by the
saved fixtures (sha256 606a80ae..., embedded in
evidence/decision1h-rollover-measurements-20261019/driver-source.json).

All additions are opt-in. Without --seed/--split/--uniform-lane the driver
behaves byte-for-byte as before (control replays must reproduce the saved CU).
  --seed S        random input/output witnesses, membership path, super-root
                  path, checkpoint sequence (nullifier hence output lane vary)
  --split 10|11   stage-1 instruction data [3,k] (both admitted, pool_route.rs:4)
  --pairs N       N < 2^20 (program cap) instead of the driver-only 1023
  --uniform-lane  build the lane state for N leaves all equal to a seeded leaf
                  digest in O(20*256) hashes (exact honest state, not a model)
  --zeroed-genesis-page  with --pairs 0: present page 0 zeroed (Genesis mode)
"""
import hashlib, sys
src, dst = sys.argv[1], sys.argv[2]
t = open(src).read()
assert hashlib.sha256(t.encode()).hexdigest() == '606a80aed4002335e54deb5a997697bca1c6ccd33dad22c64fdea76aac2507d0'
def rep(old, new, count=1):
    global t
    n = t.count(old)
    assert n == count, (old[:80], n)
    t = t.replace(old, new)

# ---- Args ----
rep("    operation: Operation,\n    tx_version: TxVersion,\n}\n",
    "    operation: Operation,\n    tx_version: TxVersion,\n    seed: Option<u64>,\n    split: u8,\n    uniform_lane: bool,\n    zeroed_genesis_page: bool,\n}\n")
rep("    let mut next_arg = 6;\n",
    "    let mut next_arg = 6;\n    let mut seed: Option<u64> = None;\n    let mut split: u8 = 10;\n    let mut uniform_lane = false;\n    let mut zeroed_genesis_page = false;\n")
rep("""                ensure!(pairs <= 1023, "--pairs must be at most 1023");""",
    """                ensure!(u64::from(pairs) < (1u64 << POOL_V1_PAIR_TREE_DEPTH), "--pairs must be below the program capacity 2^20");""")
rep("""            "--tx-version" => {""",
    """            "--seed" => {
                ensure!(seed.is_none() && next_arg + 1 < args.len(), "expected one --seed S");
                seed = Some(args[next_arg + 1].parse::<u64>().context("parse --seed")?);
                next_arg += 2;
            }
            "--split" => {
                ensure!(next_arg + 1 < args.len(), "expected --split 10|11");
                split = args[next_arg + 1].parse::<u8>().context("parse --split")?;
                ensure!(split == 10 || split == 11, "--split must be 10 or 11 (pool_route::admitted)");
                next_arg += 2;
            }
            "--uniform-lane" => { uniform_lane = true; next_arg += 1; }
            "--zeroed-genesis-page" => { zeroed_genesis_page = true; next_arg += 1; }
            "--tx-version" => {""")
rep("        operation,\n        tx_version,\n    })\n}\n",
    "        operation,\n        tx_version,\n        seed,\n        split,\n        uniform_lane,\n        zeroed_genesis_page,\n    })\n}\n")

# ---- Seeded witness helpers (appended before main) ----
helpers = r'''
struct SplitMix(u64);
impl SplitMix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn m31(&mut self) -> M31 { M31((self.next() % u64::from(P)) as u32) }
    fn digest(&mut self) -> Digest { core::array::from_fn(|_| self.m31()) }
    fn below(&mut self, n: u64) -> u64 { self.next() % n }
}

struct SeededFixture {
    input: aspis_statement::pool_v1::PoolV1PairForestInputNoteWitnessV1,
    recipient: PoolV1OutputNoteWitnessV1,
    change: PoolV1OutputNoteWitnessV1,
    withdrawal_change: PoolV1OutputNoteWitnessV1,
    anchor: Digest,
    nullifier: Digest,
    checkpoint_sequence: u64,
    lane_leaf: Digest,
    record: serde_json::Value,
}

fn seeded_fixture(seed: u64) -> Result<SeededFixture> {
    let mut rng = SplitMix(seed ^ 0x5eed_c0de_0000_0000);
    let asset_id = M31(77);
    let nullifier_key = rng.digest();
    let salt = rng.digest();
    let input_value = (WITHDRAWAL_AMOUNT + rng.below((1u64 << 30) - WITHDRAWAL_AMOUNT)) as u32;
    let input_commitment =
        pool_v1_note_commitment(&derive_owner_key(&nullifier_key), input_value, asset_id, &salt);
    let other = rng.digest();
    let selected_second = rng.below(2) == 1;
    let pair_leaf = if selected_second {
        PoolV1PairLeafWitnessV1::two_outputs(other, input_commitment)
    } else {
        PoolV1PairLeafWitnessV1::two_outputs(input_commitment, other)
    }
    .map_err(|error| anyhow!("seeded input pair: {error:?}"))?;
    let index = rng.below(1u64 << POOL_V1_PAIR_TREE_DEPTH) as u32;
    let siblings: [Digest; POOL_V1_PAIR_TREE_DEPTH] = core::array::from_fn(|_| rng.digest());
    let super_root_siblings = core::array::from_fn(|_| rng.digest());
    let super_root_directions = core::array::from_fn(|_| rng.below(2) == 1);
    let input = aspis_statement::pool_v1::PoolV1PairForestInputNoteWitnessV1 {
        pair: aspis_statement::pool_v1::pair_trace::PoolV1PairInputNoteWitnessV1 {
            nullifier_key,
            salt,
            value: input_value,
            pair_leaf,
            selected_second,
            membership: aspis_statement::pool_v1::PoolV1MembershipWitnessV1 { siblings, index },
        },
        super_root_siblings,
        super_root_directions,
    };
    let mut anchor = pair_leaf
        .leaf_digest()
        .map_err(|error| anyhow!("seeded input leaf: {error:?}"))?;
    for level in 0..POOL_V1_PAIR_TREE_DEPTH {
        anchor = if ((index >> level) & 1) == 0 {
            pool_v1_tree_parent(&anchor, &siblings[level])
        } else {
            pool_v1_tree_parent(&siblings[level], &anchor)
        };
    }
    for level in 0..super_root_siblings.len() {
        anchor = if super_root_directions[level] {
            pool_v1_tree_parent(&super_root_siblings[level], &anchor)
        } else {
            pool_v1_tree_parent(&anchor, &super_root_siblings[level])
        };
    }
    let recipient_value = rng.below(u64::from(input_value) + 1) as u32;
    let recipient = PoolV1OutputNoteWitnessV1 { owner_key: rng.digest(), salt: rng.digest(), value: recipient_value };
    let change = PoolV1OutputNoteWitnessV1 { owner_key: rng.digest(), salt: rng.digest(), value: input_value - recipient_value };
    let withdrawal_change = PoolV1OutputNoteWitnessV1 {
        owner_key: rng.digest(),
        salt: rng.digest(),
        value: input_value - WITHDRAWAL_AMOUNT as u32,
    };
    // anchor_sequence <= POOL_V1_LEAF_CAPACITY (payment_relation.rs validate_common).
    let checkpoint_sequence = 1 + rng.below((1u64 << POOL_V1_PAIR_TREE_DEPTH) - 1);
    let lane_leaf = rng.digest();
    let nullifier = pool_v1_nullifier(&nullifier_key, &salt);
    let record = serde_json::json!({
        "seed": seed,
        "input_value": input_value,
        "recipient_value": recipient_value,
        "selected_second": selected_second,
        "membership_index": index,
        "super_root_directions": super_root_directions,
        "checkpoint_sequence": checkpoint_sequence,
        "nullifier_hex": bytes_hex(&encode_digest_canonical(&nullifier)),
    });
    Ok(SeededFixture { input, recipient, change, withdrawal_change, anchor, nullifier, checkpoint_sequence, lane_leaf, record })
}

/// Exact lane state after `n` appends of the same leaf: a full subtree of 2^l
/// equal leaves has root h_l (h_0 = leaf, h_{l+1} = parent(h_l, h_l)).
fn uniform_lane_tree(n: u64, leaf: Digest) -> Result<(IncrementalMerkleTreeV1, Vec<Digest>)> {
    let empty = &POOL_V1_PAIR_EMPTY_ROOTS;
    let mut h = [leaf; POOL_V1_PAIR_TREE_DEPTH];
    for l in 1..POOL_V1_PAIR_TREE_DEPTH { h[l] = pool_v1_tree_parent(&h[l - 1], &h[l - 1]); }
    let state = |s: u64| -> IncrementalMerkleTreeV1 {
        let frontier: [Digest; POOL_V1_PAIR_TREE_DEPTH] =
            core::array::from_fn(|l| if (s >> l) & 1 == 1 { h[l] } else { empty[l] });
        let mut node = empty[0];
        for level in 0..POOL_V1_PAIR_TREE_DEPTH {
            node = if (s >> level) & 1 == 0 {
                pool_v1_tree_parent(&node, &empty[level])
            } else {
                pool_v1_tree_parent(&frontier[level], &node)
            };
        }
        IncrementalMerkleTreeV1 { next_leaf_index: s, root: node, frontier }
    };
    let tree = state(n);
    // Cross-check the closed form against one real append where possible.
    if n > 0 {
        let previous = state(n - 1);
        let appended = previous
            .append_one_with_empty_roots(leaf, empty)
            .map_err(|error| anyhow!("uniform-lane cross-check append: {error:?}"))?
            .0;
        ensure!(appended == tree, "uniform-lane closed form differs from append_one");
    }
    let first = (n / POOL_V1_ROOT_HISTORY_CAPACITY as u64) * POOL_V1_ROOT_HISTORY_CAPACITY as u64;
    let roots = (first..=n).map(|s| state(s).root).collect();
    Ok((tree, roots))
}

'''
rep("fn main() -> Result<()> {\n", helpers + "fn main() -> Result<()> {\n")

# ---- main: anchor/nullifier ----
rep("    let (historical_global_anchor, nullifier) = deterministic_anchor_and_nullifier()?;\n",
    "    let seeded = args.seed.map(seeded_fixture).transpose()?;\n"
    "    let (historical_global_anchor, nullifier) = match &seeded {\n"
    "        Some(s) => (s.anchor, s.nullifier),\n"
    "        None => deterministic_anchor_and_nullifier()?,\n"
    "    };\n")
open(dst, 'w').write(t)
print("stage A ok")

# ---- stage B: checkpoint sequence, lane, prepare, withdrawal change, split ----
t = open(dst).read()
rep("    let (historical_global_anchor, nullifier) = match &seeded {\n",
    "    let checkpoint_sequence_value = seeded.as_ref().map_or(42u64, |s| s.checkpoint_sequence);\n"
    "    let (historical_global_anchor, nullifier) = match &seeded {\n")
rep("        next_checkpoint_sequence: 43,\n", "        next_checkpoint_sequence: checkpoint_sequence_value + 1,\n")
rep("""    let mut all_lane_roots = vec![tree.root];
    for leaf in 0..args.populated_pairs {""",
"""    let mut all_lane_roots = vec![tree.root];
    if args.uniform_lane {
        let leaf = seeded.as_ref().map_or_else(|| strict_lane_digest(20_000), |s| s.lane_leaf);
        let (uniform, page_roots) = uniform_lane_tree(u64::from(args.populated_pairs), leaf)?;
        tree = uniform;
        let first = u64::from(args.populated_pairs) + 1 - page_roots.len() as u64;
        all_lane_roots = vec![[M31::ZERO; 8]; first as usize];
        all_lane_roots.extend(page_roots);
    }
    for leaf in 0..(if args.uniform_lane { 0 } else { args.populated_pairs }) {""")
rep("    let checkpoint_sequence = 42u64;\n", "    let checkpoint_sequence = checkpoint_sequence_value;\n")
rep("""    let prepared = prepare_v7_pair_forest_transfer_fixture_v1(
        master_key.to_bytes(),
        checkpoint_key.to_bytes(),
        lane_key.to_bytes(),
        checkpoint_sequence,
        DEPLOYMENT_DOMAIN_BYTES,
        live_snapshot,
    )
    .map_err(|error| anyhow!("prepare deterministic R1 fixture: {error:?}"))?;""",
"""    let prepared = match &seeded {
        Some(s) => seeded_prepare(
            s,
            master_key.to_bytes(),
            checkpoint_key.to_bytes(),
            lane_key.to_bytes(),
            checkpoint_sequence,
            live_snapshot,
        )?,
        None => prepare_v7_pair_forest_transfer_fixture_v1(
            master_key.to_bytes(),
            checkpoint_key.to_bytes(),
            lane_key.to_bytes(),
            checkpoint_sequence,
            DEPLOYMENT_DOMAIN_BYTES,
            live_snapshot,
        )
        .map_err(|error| anyhow!("prepare deterministic R1 fixture: {error:?}"))?,
    };""")
rep("""    ensure!(
        prepared.public.recipient_commitment
            == pool_v1_note_commitment(&digest(300), 600, M31(77), &digest(400))""",
"""    ensure!(
        seeded.is_some() || prepared.public.recipient_commitment
            == pool_v1_note_commitment(&digest(300), 600, M31(77), &digest(400))""")
rep("""                let change = PoolV1OutputNoteWitnessV1 {
                    owner_key: digest(700),
                    salt: digest(800),
                    value: 750,
                };""",
"""                let change = match &seeded {
                    Some(s) => s.withdrawal_change,
                    None => PoolV1OutputNoteWitnessV1 {
                        owner_key: digest(700),
                        salt: digest(800),
                        value: 750,
                    },
                };""")
rep("        data: vec![3, 10],\n", "        data: vec![3, args.split],\n")
rep("""            "stage1_instruction_data": [3, 10],""", """            "stage1_instruction_data": [3, args.split],""")
rep("""        "populated_pairs_requested": args.populated_pairs,""",
"""        "populated_pairs_requested": args.populated_pairs,
            "cu_bound_inputs": {
                "seeded": seeded.as_ref().map(|s| s.record.clone()),
                "split": args.split,
                "uniform_lane": args.uniform_lane,
                "zeroed_genesis_page": args.zeroed_genesis_page,
            },""")
rep("    put_account(&mut svm, page_key, pool_program, history_image.clone())?;\n",
"""    if args.zeroed_genesis_page {
        ensure!(lane.tree.next_leaf_index == 0, "--zeroed-genesis-page requires --pairs 0");
        put_account(&mut svm, page_key, pool_program, vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES])?;
    } else {
        put_account(&mut svm, page_key, pool_program, history_image.clone())?;
    }
""")
prep = r'''
fn seeded_prepare(
    s: &SeededFixture,
    master_account: [u8; 32],
    checkpoint_account: [u8; 32],
    selected_lane_account: [u8; 32],
    checkpoint_sequence: u64,
    output_lane_snapshot: PoolV1PairLiveSnapshotV1,
) -> Result<aspis_prover::v7_pair_forest_fixture::PreparedV7PairForestTransferFixtureV1> {
    let asset_id = M31(77);
    let witness = aspis_statement::pool_v1::PoolV1PairForestPrivateTransferWitnessV1 {
        input: s.input,
        recipient: s.recipient,
        change: s.change,
    };
    let public = aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1 {
        pool: master_account,
        deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
        anchor_sequence: checkpoint_sequence,
        anchor_root: s.anchor,
        nullifier: s.nullifier,
        asset_id,
        recipient_commitment: pool_v1_note_commitment(&s.recipient.owner_key, s.recipient.value, asset_id, &s.recipient.salt),
        change_commitment: pool_v1_note_commitment(&s.change.owner_key, s.change.value, asset_id, &s.change.salt),
    };
    let context = PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            pool: master_account,
            deployment_domain: DEPLOYMENT_DOMAIN_BYTES,
            anchor_sequence: checkpoint_sequence,
            anchor_root: s.anchor,
            asset_id,
        },
        spent_nullifiers: &[],
    };
    let compiled = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&public, &witness, context, output_lane_snapshot)
        .map_err(|error| anyhow!("compile seeded transfer witness: {error:?}"))?;
    let output_lane = pool_v1_pair_forest_output_lane_v1(&public.nullifier)
        .map_err(|error| anyhow!("seeded output lane: {error:?}"))?;
    let statement = PoolV1PairForestTerminalStatementV1::PrivateTransfer {
        common: aspis_statement::pool_v1::PoolV1PairForestTerminalCommonV1 {
            master_account,
            checkpoint_account,
            selected_lane_account,
            output_lane,
            checkpoint_sequence,
            historical_global_anchor: s.anchor,
            lane_transition: compiled.public_statement,
        },
        public,
    };
    let statement_bytes = encode_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|error| anyhow!("encode seeded statement: {error:?}"))?;
    let statement_digest = aspis_statement::pool_v1::v7_pool_pair_forest_tag73_statement_digest_v1(&statement_bytes, HOST_HASH);
    Ok(aspis_prover::v7_pair_forest_fixture::PreparedV7PairForestTransferFixtureV1 {
        public,
        witness,
        transition: compiled.public_statement,
        statement,
        statement_digest,
    })
}

'''
rep("fn main() -> Result<()> {\n", prep + "fn main() -> Result<()> {\n")
open(dst, 'w').write(t)
print("stage B ok")

# ---- stage C: marker-bump grinding (targeted bump-search site) and PDA bump record ----
t = open(dst).read()
rep("    let mut seed: Option<u64> = None;\n", "    let mut seed: Option<u64> = None;\n    let mut min_marker_attempts: u32 = 1;\n")
rep("""            "--uniform-lane" => { uniform_lane = true; next_arg += 1; }""",
"""            "--uniform-lane" => { uniform_lane = true; next_arg += 1; }
            "--min-marker-attempts" => {
                ensure!(next_arg + 1 < args.len(), "expected --min-marker-attempts K");
                min_marker_attempts = args[next_arg + 1].parse::<u32>().context("parse --min-marker-attempts")?;
                next_arg += 2;
            }""")
rep("    seed: Option<u64>,\n    split: u8,\n", "    seed: Option<u64>,\n    min_marker_attempts: u32,\n    split: u8,\n")
rep("        seed,\n        split,\n", "        seed,\n        min_marker_attempts,\n        split,\n")
rep("    let seeded = args.seed.map(seeded_fixture).transpose()?;\n",
"""    // Grind successive seeds until the nullifier-marker PDA needs at least the
    // requested number of bump attempts (attempts = 256 - bump).
    let mut ground_seed = args.seed;
    if let Some(mut s) = args.seed {
        loop {
            let candidate = seeded_fixture(s)?;
            let bump = pool_v1_nullifier_marker_address(&pool_program, &master_key, &encode_digest_canonical(&candidate.nullifier))?.1;
            if 256 - u32::from(bump) >= args.min_marker_attempts { break; }
            s = s.wrapping_add(1);
        }
        ground_seed = Some(s);
    }
    let seeded = ground_seed.map(seeded_fixture).transpose()?;
""")
rep("""                "split": args.split,""",
"""                "split": args.split,
                "min_marker_attempts": args.min_marker_attempts,
                "pda_bumps": {
                    "master": master_bump,
                    "lane": lane_bump,
                    "checkpoint": checkpoint_bump,
                    "marker": pool_v1_nullifier_marker_address(&pool_program, &master_key, &encode_digest_canonical(&nullifier))?.1,
                    "current_page": pool_v1_root_page_address(&pool_program, &lane_key, current_history_location.page_number).1,
                    "next_page": pool_v1_root_page_address(&pool_program, &lane_key, next_history_location.page_number).1,
                },""")
open(dst, 'w').write(t)
print("stage C ok")
