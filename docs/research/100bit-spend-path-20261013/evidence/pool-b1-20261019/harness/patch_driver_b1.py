#!/usr/bin/env python3
"""B1/B4 driver patch for the Pool settlement measurements (2026-10-19).

usage: patch_driver_b1.py <in pool_gate.rs> <out pool_gate.rs> [core|measure]

core     marker address = aspis_pool::pool_v1_pair_forest_nullifier_marker_address
         (create_with_seed under the master); terminal instruction data =
         ASQ8 || 4 bump hints from aspis_pool::pool_v1_pair_forest_terminal_bump_hints_v1.
         Applied to the repo driver tools/r1-cost-probe/src/bin/pool_gate.rs.
measure  core + the cu-bound sweep driver (sha256 d4b6a555..., harness of
         evidence/cu-bound-20261019) extras, all opt-in:
           --min-checkpoint-attempts K, --min-page-attempts K  grind the seed (as
               --min-marker-attempts already does for the marker) until the OLD
               canonical searches for the checkpoint / current page needed >= K
               attempts (attempts = 256 - canonical bump);
           --prefund-marker LAMPORTS  the marker address holds LAMPORTS in a
               System-owned empty account before the settlement (anyone can
               send lamports to it first).
         The grind keeps using the legacy PDA marker function: it selects seeds
         that were expensive under the old code. pda_bumps keeps those old
         bumps and records the new scheme.
"""
import hashlib, sys
src, dst, mode = sys.argv[1], sys.argv[2], (sys.argv[3] if len(sys.argv) > 3 else 'core')
t = open(src).read()
if mode == 'measure':
    assert hashlib.sha256(t.encode()).hexdigest() == 'd4b6a555e9a894de0c5c94b0d74082dafa6977736cab070ad67c80264486b03b'
def rep(old, new, count=1):
    global t
    n = t.count(old)
    assert n == count, (old[:90], n)
    t = t.replace(old, new)

# ---- core ----
rep("use aspis_pool::{\n    pool_v1_nullifier_marker_address,",
    "use aspis_pool::{\n    encode_pair_forest_terminal_instruction_data_v1, pool_v1_pair_forest_nullifier_marker_address,\n    pool_v1_pair_forest_terminal_bump_hints_v1, POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES,\n    pool_v1_nullifier_marker_address,")
rep("""    let marker_key = pool_v1_nullifier_marker_address(
        &pool_program,
        &master_key,
        &encode_digest_canonical(&nullifier),
    )?
    .0;""", """    // B1: marker = create_with_seed(master, packed SHA-256 seed, Pool).
    let marker_key = pool_v1_pair_forest_nullifier_marker_address(
        &pool_program,
        &master_key,
        &encode_digest_canonical(&nullifier),
    )?
    .0;
    // B4: Pool-only bump hints appended to ASQ8.
    let terminal_bump_hints = pool_v1_pair_forest_terminal_bump_hints_v1(
        &pool_program,
        &master_key,
        &lane_key,
        lane.tree.next_leaf_index,
        args.operation == Operation::Withdrawal,
    );
    let terminal_instruction_data =
        encode_pair_forest_terminal_instruction_data_v1(&instruction_data, terminal_bump_hints);
    ensure!(
        terminal_instruction_data.len()
            == POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES + POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES,
        "terminal instruction data length changed"
    );""")
rep("""        data: instruction_data.to_vec(),
    };
    let instruction_account_count""", """        data: terminal_instruction_data.clone(),
    };
    let instruction_account_count""")
rep('''            "instruction_bytes": instruction_data.len(),''',
    '''            "instruction_bytes": terminal_instruction_data.len(),
            "terminal_bump_hints": terminal_bump_hints.encode().to_vec(),
            "marker_address_scheme": "b1-create-with-seed(master, 7bit(sha256(aspis-marker-seed-v1||master||nullifier)[..28]), pool)",''')

if mode == 'measure':
    # pda_bumps: the marker entry is the OLD canonical PDA bump (grind record).
    rep('''                    "marker": pool_v1_nullifier_marker_address(&pool_program, &master_key, &encode_digest_canonical(&nullifier))?.1,''',
        '''                    "legacy_marker_pda_bump_not_used_by_b1": pool_v1_nullifier_marker_address(&pool_program, &master_key, &encode_digest_canonical(&nullifier))?.1,''')
    rep('''                "min_marker_attempts": args.min_marker_attempts,''',
        '''                "min_marker_attempts": args.min_marker_attempts,
                "min_checkpoint_attempts": args.min_checkpoint_attempts,
                "min_page_attempts": args.min_page_attempts,
                "prefund_marker_lamports": args.prefund_marker,
                "ground_seed": ground_seed,''')
    # Args
    rep("    min_marker_attempts: u32,\n    split: u8,",
        "    min_marker_attempts: u32,\n    min_checkpoint_attempts: u32,\n    min_page_attempts: u32,\n    prefund_marker: Option<u64>,\n    split: u8,")
    rep("    let mut min_marker_attempts: u32 = 1;\n",
        "    let mut min_marker_attempts: u32 = 1;\n    let mut min_checkpoint_attempts: u32 = 1;\n    let mut min_page_attempts: u32 = 1;\n    let mut prefund_marker: Option<u64> = None;\n")
    rep('''            "--zeroed-genesis-page" => { zeroed_genesis_page = true; next_arg += 1; }''',
        '''            "--zeroed-genesis-page" => { zeroed_genesis_page = true; next_arg += 1; }
            "--min-checkpoint-attempts" => {
                ensure!(next_arg + 1 < args.len(), "expected --min-checkpoint-attempts K");
                min_checkpoint_attempts = args[next_arg + 1].parse::<u32>().context("parse --min-checkpoint-attempts")?;
                next_arg += 2;
            }
            "--min-page-attempts" => {
                ensure!(next_arg + 1 < args.len(), "expected --min-page-attempts K");
                min_page_attempts = args[next_arg + 1].parse::<u32>().context("parse --min-page-attempts")?;
                next_arg += 2;
            }
            "--prefund-marker" => {
                ensure!(prefund_marker.is_none() && next_arg + 1 < args.len(), "expected one --prefund-marker LAMPORTS");
                let lamports = args[next_arg + 1].parse::<u64>().context("parse --prefund-marker")?;
                ensure!(lamports > 0, "--prefund-marker must be positive");
                prefund_marker = Some(lamports);
                next_arg += 2;
            }''')
    rep("        min_marker_attempts,\n", "        min_marker_attempts,\n        min_checkpoint_attempts,\n        min_page_attempts,\n        prefund_marker,\n")
    # Grind: marker (old PDA), checkpoint, current page (old canonical searches).
    rep('''            let bump = pool_v1_nullifier_marker_address(&pool_program, &master_key, &encode_digest_canonical(&candidate.nullifier))?.1;
            if 256 - u32::from(bump) >= args.min_marker_attempts { break; }''',
        '''            let bump = pool_v1_nullifier_marker_address(&pool_program, &master_key, &encode_digest_canonical(&candidate.nullifier))?.1;
            let checkpoint_old_bump = pool_v1_pair_forest_checkpoint_address(&pool_program, &master_key, candidate.checkpoint_sequence).1;
            let candidate_lane = pool_v1_pair_forest_lane_address(
                &pool_program,
                &master_key,
                pool_v1_pair_forest_output_lane_v1(&candidate.nullifier).map_err(|error| anyhow!("grind lane: {error:?}"))?,
            )?
            .0;
            let page_old_bump = pool_v1_root_page_address(
                &pool_program,
                &candidate_lane,
                root_history_location(u64::from(args.populated_pairs)).page_number,
            )
            .1;
            if 256 - u32::from(bump) >= args.min_marker_attempts
                && 256 - u32::from(checkpoint_old_bump) >= args.min_checkpoint_attempts
                && 256 - u32::from(page_old_bump) >= args.min_page_attempts
            {
                break;
            }''')
    # Prefunded marker address (System-owned, empty, LAMPORTS).
    rep('''    let mut protected_keys = vec![master_key, checkpoint_key, lane_key, page_key];''',
        '''    if let Some(lamports) = args.prefund_marker {
        svm.set_account(
            address(&marker_key),
            Account {
                lamports,
                data: Vec::new(),
                owner: address(&LegacyPubkey::default()),
                executable: false,
                rent_epoch: u64::MAX,
            },
        )
        .map_err(|error| anyhow!("prefund marker {marker_key}: {error}"))?;
    }
    let mut protected_keys = vec![master_key, checkpoint_key, lane_key, page_key];''')
open(dst, 'w').write(t)
print('patched', mode, hashlib.sha256(t.encode()).hexdigest())
