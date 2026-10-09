//! Task-owned LiteSVM extension; never linked by the repository/default build.
use super::*;
use std::collections::BTreeMap;
const B_ID: [u8; 32] = [0xb8; 32];
const D: &[u8] = b"aspis/research/v8/atomic-message/v1";
fn digest(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for p in parts {
        h.update(p);
    }
    h.finalize().into()
}
fn parent(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    digest(&[D, b"/node", a, b])
}
fn empties() -> Vec<[u8; 32]> {
    let mut z = vec![digest(&[D, b"/empty"])];
    for i in 0..20 {
        z.push(parent(&z[i], &z[i]));
    }
    z
}
fn sparse(leaves: &[[u8; 32]]) -> ([u8; 32], Vec<[u8; 32]>) {
    let z = empties();
    let mut nodes: BTreeMap<usize, [u8; 32]> = leaves.iter().copied().enumerate().collect();
    let mut index = leaves.len();
    let mut path = vec![];
    for level in 0..20 {
        path.push(*nodes.get(&(index ^ 1)).unwrap_or(&z[level]));
        let mut next = BTreeMap::new();
        for k in nodes.keys() {
            let k = k / 2;
            next.insert(
                k,
                parent(
                    nodes.get(&(2 * k)).unwrap_or(&z[level]),
                    nodes.get(&(2 * k + 1)).unwrap_or(&z[level]),
                ),
            );
        }
        nodes = next;
        index /= 2;
    }
    (*nodes.get(&0).unwrap_or(&z[20]), path)
}
fn tx(
    svm: &LiteSVM,
    payer: &Keypair,
    instructions: &[Instruction],
) -> Result<VersionedTransaction> {
    let config = TransactionConfig::empty()
        .with_priority_fee(10_000)
        .with_compute_unit_limit(1_200_000)
        .with_loaded_accounts_data_size_limit(8 * 1024 * 1024)
        .with_heap_size(256 * 1024);
    let msg = v1::Message::try_compile_with_config(
        &payer.pubkey(),
        instructions,
        svm.latest_blockhash(),
        config,
    )?;
    Ok(VersionedTransaction::try_new(
        VersionedMessage::V1(msg),
        &[payer],
    )?)
}
fn triplet(pre: Instruction) -> Vec<Instruction> {
    let n = pre.accounts.len() - 3;
    let source = Instruction {
        program_id: address(&legacy(POOL_PROGRAM_BYTES)),
        accounts: pre.accounts[..n].to_vec(),
        data: pre.data[792..].to_vec(),
    };
    let mut final_ix = pre.clone();
    final_ix.data[..4].copy_from_slice(b"ATF8");
    vec![pre, source, final_ix]
}
fn execute(
    svm: &mut LiteSVM,
    payer: &Keypair,
    instructions: &[Instruction],
    success: bool,
) -> Result<serde_json::Value> {
    let tx = tx(svm, payer, instructions)?;
    let wire = wincode::serialize(&tx)?;
    ensure!(wire.len() <= 4096, "packet limit");
    // Independently inspect the SIGNED wire config, not a driver argument.
    ensure!(
        wire[0] == 0x81 && u32::from_le_bytes(wire[4..8].try_into().unwrap()) == 31,
        "TxV1 header/config mask"
    );
    let address_count = wire[41] as usize;
    let instruction_count = wire[40] as usize;
    ensure!(
        address_count <= 64 && instruction_count <= 64,
        "TxV1 account/instruction limits"
    );
    let cfg = 42 + 32 * address_count;
    ensure!(u64::from_le_bytes(wire[cfg..cfg + 8].try_into().unwrap()) == 10000);
    ensure!(u32::from_le_bytes(wire[cfg + 8..cfg + 12].try_into().unwrap()) == 1200000);
    ensure!(u32::from_le_bytes(wire[cfg + 12..cfg + 16].try_into().unwrap()) == 8388608);
    ensure!(u32::from_le_bytes(wire[cfg + 16..cfg + 20].try_into().unwrap()) == 262144);
    let fee_before = svm.get_account(&payer.pubkey()).unwrap().lamports;
    let sim = svm.simulate_transaction(tx.clone());
    let res = svm.send_transaction(tx);
    let (meta, error) = match res {
        Ok(meta) => {
            ensure!(success, "unexpected acceptance");
            ensure!(sim.unwrap().meta == meta, "simulation differs");
            (meta, None)
        }
        Err(e) => {
            ensure!(
                !success,
                "unexpected rejection {:?}\n{}",
                e.err,
                e.meta.pretty_logs()
            );
            let s = sim.unwrap_err();
            ensure!(
                s.err == e.err && s.meta == e.meta,
                "failure simulation differs"
            );
            (e.meta, Some(format!("{:?}", e.err)))
        }
    };
    ensure!(meta.compute_units_consumed <= 1_200_000, "CU gate");
    let fee_after = svm.get_account(&payer.pubkey()).unwrap().lamports;
    Ok(
        serde_json::json!({"accepted":success,"cu":meta.compute_units_consumed,"signed_transaction_bytes":wire.len(),
        "signed_transaction_sha256":sha256_hex(&wire),"signed_transaction_hex":bytes_hex(&wire),"address_count":address_count,"instruction_count":instruction_count,"logs":meta.logs,"error":error,
        "payer_lamport_decrease":fee_before-fee_after,"configured_cu":1_200_000,"heap_bytes":262144,"loaded_data_limit":8388608,
        "instructions":instructions.iter().map(|i|serde_json::json!({"program":i.program_id.to_string(),"data_hex":bytes_hex(&i.data),
            "accounts":i.accounts.iter().map(|a|serde_json::json!({"key":a.pubkey.to_string(),"signer":a.is_signer,"writable":a.is_writable})).collect::<Vec<_>>()})).collect::<Vec<_>>(),
        "return_program":meta.return_data.program_id.to_string(),"return_bytes":meta.return_data.data.len()}),
    )
}
fn snapshots_hash(s: &[Option<Account>]) -> String {
    let mut h = Sha256::new();
    for a in s {
        match a {
            None => h.update([0]),
            Some(a) => {
                h.update([1]);
                h.update(a.lamports.to_le_bytes());
                h.update(a.owner.as_ref());
                h.update([a.executable as u8]);
                h.update((a.data.len() as u64).to_le_bytes());
                h.update(&a.data);
            }
        }
    }
    bytes_hex(&h.finalize())
}
fn case(
    base: &LiteSVM,
    payer: &Keypair,
    keys: &[LegacyPubkey],
    name: &str,
    instructions: Vec<Instruction>,
    edits: Vec<(LegacyPubkey, Account)>,
    success: bool,
    after_a: bool,
    after_b: bool,
) -> Result<(LiteSVM, serde_json::Value)> {
    let mut svm = base.clone();
    svm.expire_blockhash();
    for (k, a) in edits {
        svm.set_account(address(&k), a)?;
    }
    let before = snapshot(&svm, keys);
    let mut result = execute(&mut svm, payer, &instructions, success)?;
    let after = snapshot(&svm, keys);
    if !success {
        ensure!(before == after, "{name}: partial success!");
    }
    let logs = result["logs"].as_array().unwrap();
    let a_seen = logs
        .iter()
        .any(|s| s.as_str().unwrap().contains("atomic:A-settled-real-pool"));
    let b_seen = logs
        .iter()
        .any(|s| s.as_str().unwrap().contains("Program data: YXRvbWljOnJlY2VpcHQtdjE="));
    let verifier_success = logs
        .iter()
        .any(|s| s.as_str().unwrap() == format!("Program {} success", VERIFIER_PROGRAM_ID));
    ensure!(
        a_seen == after_a,
        "{name}: source settlement trace mismatch"
    );
    if after_a {
        ensure!(verifier_success, "{name}: no real verifier success");
    }
    if after_b {
        ensure!(b_seen, "{name}: no destination update trace");
    }
    result["name"] = name.into();
    result["protected_before_sha256"] = snapshots_hash(&before).into();
    result["protected_after_sha256"] = snapshots_hash(&after).into();
    result["all_protected_unchanged"] = (before == after).into();
    result["real_verifier_success"] = verifier_success.into();
    result["source_provisionally_settled"] = a_seen.into();
    println!(
        "ATOMIC_CASE {name} accepted={success} cu={} after_a={a_seen}",
        result["cu"]
    );
    Ok((svm, result))
}

pub(super) fn run(
    svm: &mut LiteSVM,
    payer: &Keypair,
    args: &Args,
    original_keys: &[LegacyPubkey],
    original: Instruction,
    lane: &PoolV1PairForestLaneStateV1,
    afterstate: &PoolV1PairVerifiedAfterstateV1,
    request: &PoolV1PairForestTerminalRequestV1,
) -> Result<()> {
    ensure!(
        args.operation == Operation::Transfer
            && args.scenario == Scenario::Success
            && args.runtime_compute_limit == 1_400_000
    );
    let ex = PathBuf::from(env::var("ASPIS_ATOMIC_EXPERIMENT")?);
    let elf = fs::read(ex.join("../../../artifacts/inbox/aspis_v8_atomic_inbox.so"))?;
    let bprogram = legacy(B_ID);
    svm.add_program(address(&bprogram), &elf)?;
    let public = match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p) => p,
        _ => unreachable!(),
    };
    let master = legacy(public.pool);
    let asset = public.asset_id.0.to_le_bytes();
    let bkey = LegacyPubkey::find_program_address(
        &[b"aspis-v8-inbox-v1", master.as_ref(), &asset],
        &bprogram,
    )
    .0;
    let mut baseline_svm = svm.clone();
    let baseline = execute(&mut baseline_svm, payer, &[original.clone()], true)?;
    let expected_a = snapshot(&baseline_svm, original_keys);
    ensure!(
        decode_pool_v1_pair_forest_lane_state_v1(
            &expected_a[2].as_ref().unwrap().data,
            &POOL_V1_PAIR_EMPTY_ROOTS
        )
        .unwrap()
        .tree
        .root
            == afterstate.next_root
    );
    let before_init = snapshot(svm, original_keys);
    let mut init_data = b"ABI8\x01\x14\0\0".to_vec();
    init_data.extend(public.pool);
    init_data.extend(asset);
    let init_ix = Instruction {
        program_id: address(&bprogram),
        accounts: vec![
            meta(bkey, true),
            signer_meta(legacy(payer.pubkey().to_bytes()), true),
            meta(LegacyPubkey::default(), false),
            meta(master, false),
        ],
        data: init_data,
    };
    let init = execute(svm, payer, &[init_ix.clone()], true)?;
    ensure!(
        snapshot(svm, original_keys) == before_init,
        "initialization changed A"
    );
    let mut baccount = svm.get_account(&address(&bkey)).unwrap();
    ensure!(
        baccount.data.len() == 116
            && baccount.data[..8] == *b"BIX8\x01\x14\0\0"
            && baccount.data[52..84] == empties()[20]
    );
    let n: usize = env::var("ASPIS_ATOMIC_B_COUNT")
        .unwrap_or("13".into())
        .parse()?;
    ensure!(n <= 4095, "bounded synthetic history");
    let leaves: Vec<_> = (0..n)
        .map(|i| digest(&[D, b"/fixture", &(i as u64).to_le_bytes()]))
        .collect();
    let (broot, path) = sparse(&leaves);
    // Nonempty histories are explicit synthetic fixture construction, not
    // evidence that these previous messages were verified on chain.
    baccount.data[44..52].copy_from_slice(&(n as u64).to_le_bytes());
    baccount.data[52..84].copy_from_slice(&broot);
    if n > 0 {
        baccount.data[84..116].copy_from_slice(&leaves[n - 1]);
    }
    svm.set_account(address(&bkey), baccount.clone())?;
    let release = digest(&[D, b"/release:pool-asq8:sha256-depth20:message-only"]);
    let aseq = lane.tree.next_leaf_index;
    let aroot = encode_digest_canonical(&lane.tree.root);
    let anew = encode_digest_canonical(&afterstate.next_root);
    let asq = encode_pool_v1_pair_forest_terminal_request_v1(request).unwrap();
    let leaf = digest(&[
        D,
        &release,
        &B_ID,
        &POOL_PROGRAM_BYTES,
        &LegacyPubkey::from_str(VERIFIER_PROGRAM_ID)?.to_bytes(),
        &public.pool,
        &original_keys[2].to_bytes(),
        &PROOF_ACCOUNT_BYTES,
        &aseq.to_le_bytes(),
        &aroot,
        &afterstate.next_pair_index.to_le_bytes(),
        &anew,
        &bkey.to_bytes(),
        &(n as u64).to_le_bytes(),
        &broot,
        &asq,
    ]);
    let mut new_leaves = leaves.clone();
    new_leaves.push(leaf);
    let bnew = sparse(&new_leaves).0;
    let mut data = b"ATH8\x01\x14\0\0".to_vec();
    data.extend((n as u64).to_le_bytes());
    data.extend(broot);
    data.extend(bnew);
    data.extend(aseq.to_le_bytes());
    data.extend(aroot);
    data.extend(leaf);
    for s in path {
        data.extend(s);
    }
    data.extend(asq);
    ensure!(data.len() == 1112);
    let mut accounts = original.accounts.clone();
    accounts.push(meta(legacy(POOL_PROGRAM_BYTES), false));
    accounts.push(meta(bkey, true));
    accounts.push(meta(
        LegacyPubkey::from_str("Sysvar1nstructions1111111111111111111111111")?,
        false,
    ));
    let atomic = Instruction {
        program_id: address(&bprogram),
        accounts,
        data,
    };
    let mut keys = original_keys.to_vec();
    keys.push(bkey);
    let mut cases = vec![];
    let (settled, happy) = case(
        svm,
        payer,
        &keys,
        "success",
        triplet(atomic.clone()),
        vec![],
        true,
        true,
        true,
    )?;
    ensure!(
        snapshot(&settled, original_keys) == expected_a,
        "atomic source diverges from real baseline"
    );
    let bafter = settled.get_account(&address(&bkey)).unwrap();
    let mut bexpected = baccount.clone();
    bexpected.data[44..52].copy_from_slice(&((n + 1) as u64).to_le_bytes());
    bexpected.data[52..84].copy_from_slice(&bnew);
    bexpected.data[84..116].copy_from_slice(&leaf);
    ensure!(bafter == bexpected, "destination reference mismatch");
    cases.push(happy);
    let mut features = LiteSVM::mainnet_feature_set();
    features.activate(&"txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL".parse().unwrap(),0);
    let mut active_features: Vec<_> = features
        .active()
        .iter()
        .map(|(key, slot)| (key.to_string(), *slot))
        .collect();
    active_features.sort();
    let txv1_active = active_features
        .iter()
        .find(|(k, _)| k == "txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL");
    let deep = env::var("ASPIS_ATOMIC_DEEP").as_deref() == Ok("1");
    // Every new public field, every destination level, and every ASQ8 public
    // field gets a named mutation. Hash-byte sweeps are separate host controls.
    let mut mutations = vec![
        ("magic".to_string(), 0, false),
        ("version".into(), 4, false),
        ("depth".into(), 5, false),
        ("reserved".into(), 6, false),
        ("b-sequence".into(), 8, false),
        ("b-old-root".into(), 16, false),
        ("b-new-root".into(), 48, true),
        ("a-sequence".into(), 80, false),
        ("a-old-root".into(), 88, false),
        ("handoff".into(), 120, true),
    ];
    if deep {
        for i in 0..20 {
            mutations.push((format!("destination-path-{i}"), 152 + 32 * i, true));
        }
        // ASQ8 framing: public ASPS begins at 104; exact source format reviewed.
        for (name, offset) in [
            ("asq-magic", 0),
            ("asq-version", 4),
            ("profile", 8),
            ("release", 40),
            ("pool-program", 72),
            ("payment-magic", 104),
            ("source-master", 112),
            ("domain", 144),
            ("anchor-sequence", 176),
            ("membership-root", 184),
            ("nullifier", 216),
            ("asset", 248),
            ("fee-or-value-reserved", 252),
            ("recipient", 256),
            ("change", 288),
        ] {
            mutations.push((name.into(), 792 + offset, false));
        }
    }
    for (name, pos, after_a) in mutations {
        let mut bad = atomic.clone();
        bad.data[pos] ^= 1;
        let (_, r) = case(
            svm,
            payer,
            &keys,
            &name,
            triplet(bad),
            vec![],
            false,
            after_a,
            false,
        )?;
        cases.push(r);
    }
    let fail_ix = Instruction {
        program_id: address(&LegacyPubkey::default()),
        accounts: vec![],
        data: vec![255],
    };
    let (_, r) = case(
        svm,
        payer,
        &keys,
        "later-instruction-failure",
        {
            let mut v = triplet(atomic.clone());
            v.push(fail_ix);
            v
        },
        vec![],
        false,
        true,
        true,
    )?;
    cases.push(r);
    let (_, r) = case(
        &settled,
        payer,
        &keys,
        "exact-replay-fresh-blockhash",
        triplet(atomic.clone()),
        vec![],
        false,
        false,
        false,
    )?;
    cases.push(r);
    let mut replay = atomic.clone();
    replay.data[8..16].copy_from_slice(&((n + 1) as u64).to_le_bytes());
    replay.data[16..48].copy_from_slice(&bnew);
    replay.data[80..88].copy_from_slice(&afterstate.next_pair_index.to_le_bytes());
    replay.data[88..120].copy_from_slice(&anew);
    let (_, r) = case(
        &settled,
        payer,
        &keys,
        "reuse-nullifier-refreshed-live-roots",
        triplet(replay),
        vec![],
        false,
        false,
        false,
    )?;
    cases.push(r);
    let (_, r) = case(
        &settled,
        payer,
        &keys,
        "inbox-reinitialize-occupied",
        vec![init_ix],
        vec![],
        false,
        false,
        false,
    )?;
    cases.push(r);
    if deep {
        let trio = triplet(atomic.clone());
        let mut mismatch = trio.clone();
        mismatch[2].data[120] ^= 1;
        for (name, ixs) in [
            ("missing-final", trio[..2].to_vec()),
            ("missing-source", vec![trio[0].clone(), trio[2].clone()]),
            ("missing-precheck", trio[1..].to_vec()),
            ("final-only", vec![trio[2].clone()]),
            ("mismatched-final", mismatch),
            (
                "intervening-instruction",
                vec![
                    trio[0].clone(),
                    Instruction {
                        program_id: address(&LegacyPubkey::default()),
                        accounts: vec![],
                        data: vec![255],
                    },
                    trio[1].clone(),
                    trio[2].clone(),
                ],
            ),
        ] {
            let (_, r) = case(svm, payer, &keys, name, ixs, vec![], false, false, false)?;
            cases.push(r);
        }
        let mut shifted = triplet(atomic.clone());
        shifted[2].accounts.pop();
        let (_, r) = case(
            svm,
            payer,
            &keys,
            "mismatched-final-accounts",
            shifted,
            vec![],
            false,
            false,
            false,
        )?;
        cases.push(r);
        let mut routed = atomic.clone();
        let last = routed.accounts.len() - 2;
        routed.accounts[last].pubkey = address(
            &LegacyPubkey::find_program_address(
                &[
                    b"aspis-v8-inbox-v1",
                    master.as_ref(),
                    &(public.asset_id.0 + 1).to_le_bytes(),
                ],
                &bprogram,
            )
            .0,
        );
        let (_, r) = case(
            &settled,
            payer,
            &keys,
            "same-note-different-destination",
            triplet(routed),
            vec![],
            false,
            false,
            false,
        )?;
        cases.push(r);
        let marker = original_keys[if args.populated_pairs == 255 { 5 } else { 4 }];
        let allocate = solana_program::system_instruction::allocate(&marker, 0);
        let bad_close = Instruction {
            program_id: address(&allocate.program_id),
            accounts: allocate
                .accounts
                .iter()
                .map(|a| meta(a.pubkey, a.is_writable))
                .collect(),
            data: allocate.data,
        };
        let (_, r) = case(
            &settled,
            payer,
            &keys,
            "occupied-nullifier-system-reallocate",
            vec![bad_close],
            vec![],
            false,
            false,
            false,
        )?;
        cases.push(r);
        let proof_key = legacy(PROOF_ACCOUNT_BYTES);
        let mut proof = svm.get_account(&address(&proof_key)).unwrap();
        for (name, offset) in [
            ("invalid-proof", 40 + 688),
            ("unsealed-proof", 8),
            ("invalid-afterstate", 40 + 16),
        ] {
            let mut p = proof.clone();
            p.data[offset] ^= 1;
            let (_, r) = case(
                svm,
                payer,
                &keys,
                name,
                triplet(atomic.clone()),
                vec![(proof_key, p)],
                false,
                false,
                false,
            )?;
            cases.push(r);
        }
        proof.owner = address(&legacy([0xfe; 32]));
        let (_, r) = case(
            svm,
            payer,
            &keys,
            "wrong-proof-owner",
            triplet(atomic.clone()),
            vec![(proof_key, proof)],
            false,
            false,
            false,
        )?;
        cases.push(r);
        for (name, mutated) in [
            ("inbox-owner", {
                let mut a = baccount.clone();
                a.owner = address(&legacy(POOL_PROGRAM_BYTES));
                a
            }),
            ("inbox-reserved", {
                let mut a = baccount.clone();
                a.data[6] = 1;
                a
            }),
            ("inbox-trailing", {
                let mut a = baccount.clone();
                a.data.push(0);
                a
            }),
            ("stale-live-B", {
                let mut a = baccount.clone();
                a.data[52] ^= 1;
                a
            }),
            ("altered-live-B-sequence", {
                let mut a = baccount.clone();
                a.data[44] ^= 1;
                a
            }),
        ] {
            let (_, r) = case(
                svm,
                payer,
                &keys,
                name,
                triplet(atomic.clone()),
                vec![(bkey, mutated)],
                false,
                false,
                false,
            )?;
            cases.push(r);
        }
        let updated_lane = expected_a[2].as_ref().unwrap().clone();
        let (_, r) = case(
            svm,
            payer,
            &keys,
            "conflicting-spend-live-A",
            triplet(atomic.clone()),
            vec![(original_keys[2], updated_lane)],
            false,
            false,
            false,
        )?;
        cases.push(r);
        for name in [
            "alias-A-B",
            "swapped-A-accounts",
            "wrong-destination",
            "readonly-B",
            "wrong-pool-program",
            "counterfeit-verifier",
            "substituted-proof",
        ] {
            let mut ix = atomic.clone();
            let end = ix.accounts.len() - 1;
            match name {
                "alias-A-B" => ix.accounts[end - 1].pubkey = ix.accounts[2].pubkey,
                "swapped-A-accounts" => ix.accounts.swap(0, 2),
                "wrong-destination" => ix.accounts[end - 1].pubkey = address(&legacy([0xb9; 32])),
                "readonly-B" => ix.accounts[end - 1].is_writable = false,
                "wrong-pool-program" => ix.accounts[end - 2].pubkey = address(&legacy([0xfa; 32])),
                "counterfeit-verifier" => {
                    ix.accounts[end - 4].pubkey = address(&legacy([0xfb; 32]))
                }
                "substituted-proof" => ix.accounts[end - 3].pubkey = address(&legacy([0xfc; 32])),
                _ => unreachable!(),
            }
            let (_, r) = case(
                svm,
                payer,
                &keys,
                name,
                triplet(ix),
                vec![],
                false,
                false,
                false,
            )?;
            cases.push(r);
        }
        // A diagnostic double is used only for rejection. The accepted cases
        // above always load the recorded real verifier. Registry code identity
        // and the Pool's returned-result checks remain active.
        let mut fake = svm.clone();
        fake.add_program(
            address(&LegacyPubkey::from_str(VERIFIER_PROGRAM_ID)?),
            &fs::read(&args.result_double_program)?,
        )?;
        let (_, r) = case(
            &fake,
            payer,
            &keys,
            "counterfeit-verifier-ELF",
            triplet(atomic.clone()),
            vec![],
            false,
            false,
            false,
        )?;
        cases.push(r);
    }
    let result = serde_json::json!({"schema":"aspis.v8.atomic-two-root.v1","base":"4aaa61e679189b2cf76bfc25c2e3ff8d5c76341e",
        "milestone":"I; ZK source plus deterministic message inbox; separate owners","baseline":baseline,"initialize_B":init,"cases":cases,
        "source_pairs":args.populated_pairs,"destination_prior_receipts":n,"destination_depth":20,"source_membership_depth":24,
        "proof_bytes":fs::metadata(&args.proof_fixture)?.len(),"proof_sha256":sha256_hex(&fs::read(&args.proof_fixture)?),
        "inbox_elf_sha256":sha256_hex(&elf),"inbox_elf_bytes":elf.len(),"inbox_account_bytes":116,
        "reference":{"a_old_sequence":aseq,"a_new_sequence":afterstate.next_pair_index,"a_old_root":bytes_hex(&aroot),"a_new_root":bytes_hex(&anew),
            "b_old_root":bytes_hex(&broot),"b_new_root":bytes_hex(&bnew),"receipt":bytes_hex(&leaf),"b_account":bytes_hex(&bkey.to_bytes()),
            "b_program":bytes_hex(&B_ID),"source_program":bytes_hex(&POOL_PROGRAM_BYTES),"verifier":bytes_hex(&LegacyPubkey::from_str(VERIFIER_PROGRAM_ID)?.to_bytes()),
            "source_master":bytes_hex(&public.pool),"source_lane":bytes_hex(&original_keys[2].to_bytes()),"proof_account":bytes_hex(&PROOF_ACCOUNT_BYTES),"asq8":bytes_hex(&asq)},
        "runtime":"LiteSVM 0.16.0; inherited feature snapshot; runtime 4.2.1","runtime_active_features":active_features,"local_txv1_feature_activation":txv1_active,"cu_limit":1200000,"packet_limit":4096,
        "proof_upload":"preloaded sealed synthetic fixture; upload lifecycle is separately unmeasured","no_global_security_claim":true});
    fs::write(&args.evidence, serde_json::to_vec_pretty(&result)?)?;
    Ok(())
}
