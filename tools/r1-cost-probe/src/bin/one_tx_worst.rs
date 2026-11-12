//! ASPIS WORST-CASE COMPUTE PROBE (11 November 2026). Measurements, not proofs.
//!
//! Builds Pool states that the two recorded devnet payments cannot reach (any lane
//! position, so the same-page, genesis and page-rollover paths of the terminal
//! handler; both operations; three marker funding states), proves a fresh payment
//! against each state with the deterministic insecure fixture witness, re-packs the
//! proof into the summed format and runs the one-transaction settlement in LiteSVM
//! at the real 1,400,000 CU limit with the deployed Pool ELF and each given
//! verifier ELF at the devnet verifier address.
//!
//! Everything the Pool and the verifier authenticate but the fixture does not
//! choose is taken from the recorded devnet settlement: program ids, the master
//! account (its asset id set to the fixture's 77), registry and entry, payer, the
//! verifier-owned seventh account, mint, vault, vault authority, token program,
//! clock slot and devnet rent. The fixture chooses the checkpoint (sequence 42,
//! global root = the fixture anchor), the output lane and its history pages, the
//! nullifier marker address and, for withdrawals, the destination token account
//! (a copy of the recorded destination's data at the fixture's address).
//!
//! Signature verification is off (no recorded keys). For each run the tool checks
//! the final state: success writes the expected lane image, history page and
//! marker and moves exactly the withdrawal amount; a run at a compute limit one
//! unit below the measured cost fails and changes nothing but the payer's fee.
//!
//! usage: one_tx_worst <transactions.json> <pool.so> <out.json> <specs> <label=elf.so>...
//!   specs: comma-separated `op:N:seed:mode`, op = transfer|withdrawal, N = the
//!   lane's leaf count before the payment (0..=1023), seed = fixture proof seed
//!   byte, mode = full (three marker states + below-limit run) | basic (marker
//!   absent only) | genesis (N must be 0; page 0 left zeroed, full runs) |
//!   neg-<where>-<at>: a NEGATIVE scenario (added for the Pool page zero check,
//!   POOL-PAGE-CHECK.md): one non-zero byte (0x01) planted in a history page that the
//!   Pool requires to be zero there, marker absent, one run at the real limit that
//!   must fail and change nothing but the payer's fee. <where> = tail (unused tail
//!   of the current page, same-page path only) | next (the next page at rollover,
//!   rollover positions only) | genesis (page 0 zeroed except the planted byte,
//!   N must be 0); <at> = first | mid | last position of that region.
//!   neg-<master|checkpoint|lane>-<byte>: a NEGATIVE scenario for the Pool's account decoders: the
//!   byte at that offset of the master, checkpoint or lane account is XORed with 0x01, marker absent,
//!   one run at the real limit that must fail and change nothing but the payer's fee.
//!   Every run also records a sha256 of all watched accounts after the run
//!   (`post_state_sha256`), so runs with different Pool ELFs can be compared.
use anyhow::{anyhow, ensure, Context, Result};
use aspis_core::field::{M31, P};
use aspis_pool::{
    encode_pair_forest_terminal_instruction_data_v1, pool_v1_pair_forest_checkpoint_address,
    pool_v1_pair_forest_lane_address, pool_v1_pair_forest_nullifier_marker_address,
    pool_v1_pair_forest_terminal_bump_hints_v1, pool_v1_root_page_address, POOL_V1_PAIR_EMPTY_ROOTS,
};
use aspis_prover::{r0_fixture::statement_public, v7_pair_forest_fixture::prepare_v7_pair_forest_transfer_fixture_v1, HOST_HASH};
use aspis_r1_cost_probe::{multiproof, prover, transport::Variant, verifier::candidate::one_tx};
use aspis_statement::pool_v1::root_history::{append_root_history_page_bytes_v1, initialize_root_history_page_bytes_v1, root_history_location};
use aspis_statement::{
    encode_digest_canonical,
    pool_v1::{
        compile_pool_v1_pair_forest_private_transfer_merged_c1_v1, compile_pool_v1_pair_forest_withdrawal_merged_c1_v1,
        decode_pool_v1_pair_forest_master_v1, decode_pool_v1_pair_forest_terminal_request_v1,
        encode_pool_v1_pair_forest_checkpoint_v1, encode_pool_v1_pair_forest_lane_state_v1, encode_pool_v1_pair_forest_master_v1,
        encode_pool_v1_pair_forest_terminal_request_v1, encode_pool_v1_pair_verified_afterstate_v1, pool_v1_note_commitment,
        pool_v1_pair_forest_output_lane_v1, IncrementalMerkleTreeV1, PoolV1OutputNoteWitnessV1, PoolV1PairForestCheckpointV1,
        PoolV1PairForestLaneStateV1, PoolV1PairForestTerminalPaymentV1, PoolV1PairForestTerminalRequestV1,
        PoolV1PairForestTerminalStatementV1, PoolV1PairForestWithdrawalWitnessV1, PoolV1PairLiveSnapshotV1,
        PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1, PoolV1WithdrawalPublicV1, POOL_V1_PAIR_TREE_DEPTH,
        POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, POOL_V1_ROOT_HISTORY_CAPACITY, POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES,
    },
    poseidon2::Digest,
};
use litesvm::LiteSVM;
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{account_meta::AccountMeta, Instruction};
use solana_message::Message;
use solana_program::pubkey::Pubkey as LegacyPubkey;
use solana_transaction::Transaction;
use std::{env, fs, path::Path, str::FromStr, time::Instant};

const WITHDRAWAL_AMOUNT: u32 = 250;
const DESTINATION_TOKEN_ACCOUNT_BYTES: [u8; 32] = [0x49; 32];
const CHECKPOINT_SEQUENCE: u64 = 42;
const LAMPORTS_PER_BYTE: u64 = 5_080;
const SYSTEM: &str = "11111111111111111111111111111111";

fn sha(b: &[u8]) -> String {
    format!("{:x}", Sha256::digest(b))
}
fn legacy(s: &str) -> Result<LegacyPubkey> {
    LegacyPubkey::from_str(s).map_err(|e| anyhow!("key {s}: {e:?}"))
}
fn addr(k: &LegacyPubkey) -> Address {
    Address::new_from_array(k.to_bytes())
}
fn base58(a: &Address) -> String {
    LegacyPubkey::new_from_array(a.to_bytes()).to_string()
}
fn rent_for(space: usize) -> u64 {
    (128 + space as u64) * LAMPORTS_PER_BYTE
}
fn unhex(s: &str) -> Result<Vec<u8>> {
    ensure!(s.len() % 2 == 0, "odd hex");
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|e| anyhow!("hex: {e}"))).collect()
}
fn unbase64(s: &str) -> Result<Vec<u8>> {
    let mut out = Vec::with_capacity(s.len() / 4 * 3);
    let (mut acc, mut bits) = (0u32, 0u32);
    for c in s.bytes() {
        let v = match c {
            b'A'..=b'Z' => c - b'A',
            b'a'..=b'z' => c - b'a' + 26,
            b'0'..=b'9' => c - b'0' + 52,
            b'+' => 62,
            b'/' => 63,
            b'=' => break,
            _ => return Err(anyhow!("base64 byte {c}")),
        };
        acc = (acc << 6) | u32::from(v);
        bits += 6;
        if bits >= 8 {
            bits -= 8;
            out.push((acc >> bits) as u8);
            acc &= (1 << bits) - 1;
        }
    }
    Ok(out)
}
// The deterministic fixture's digests (as in pool_gate.rs).
fn digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31((seed + 17 * index as u32 + 1) % P))
}
fn strict_lane_digest(seed: u32) -> Digest {
    core::array::from_fn(|index| M31((seed + 17 * index as u32) % P))
}
#[derive(Clone, Copy)]
struct Sha;
impl aspis_core::Digest32 for Sha {
    fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
        let mut d = Sha256::new();
        for p in parts {
            d.update(p);
        }
        d.finalize().into()
    }
}

/// Recorded accounts of one settlement (non-executable ones), keyed by base58.
fn recorded_accounts(tx: &Value) -> Result<Vec<(LegacyPubkey, Account)>> {
    let mut out = vec![];
    for a in tx["pre"]["accounts"].as_array().context("pre.accounts")? {
        if !a["exists"].as_bool().unwrap_or(false) || a["executable"].as_bool().unwrap_or(false) {
            continue;
        }
        let data = unbase64(a["data_base64"].as_str().context("data")?)?;
        out.push((
            legacy(a["key"].as_str().context("key")?)?,
            Account { lamports: a["lamports"].as_u64().context("lamports")?, data, owner: addr(&legacy(a["owner"].as_str().context("owner")?)?), executable: false, rent_epoch: u64::MAX },
        ));
    }
    Ok(out)
}
fn consumed(logs: &[String], program: &str) -> Option<u64> {
    logs.iter().rev().find_map(|l| l.strip_prefix(&format!("Program {program} consumed "))?.split_whitespace().next()?.parse().ok())
}

/// Number of exchanges the verifier's insertion sort (`merged_keys`) makes.
fn insertion_swaps(queries: &[u32; 22], folded: bool) -> usize {
    let mut keys = [0u64; 22];
    for j in 0..22 {
        let index = if folded { queries[j] / 4 } else { queries[j] };
        keys[j] = (u64::from(index) << 8) | j as u64;
    }
    let mut swaps = 0;
    for i in 1..22 {
        let mut j = i;
        while j > 0 && keys[j - 1] > keys[j] {
            keys.swap(j - 1, j);
            swaps += 1;
            j -= 1;
        }
    }
    swaps
}

struct Spec {
    withdrawal: bool,
    leaves: u64,
    seed: u8,
    mode: String,
}
fn parse_specs(s: &str) -> Result<Vec<Spec>> {
    s.split(',')
        .map(|item| {
            let f: Vec<&str> = item.split(':').collect();
            ensure!(f.len() == 4, "spec {item}: op:N:seed:mode");
            let withdrawal = match f[0] {
                "transfer" => false,
                "withdrawal" => true,
                o => return Err(anyhow!("op {o}")),
            };
            let leaves: u64 = f[1].parse()?;
            ensure!(leaves <= 1023, "N at most 1023");
            let negative = f[3].strip_prefix("neg-").and_then(|r| r.split_once('-'));
            ensure!(
                matches!(f[3], "full" | "basic" | "genesis")
                    || matches!(negative, Some(("tail" | "next" | "genesis", "first" | "mid" | "last")))
                    || matches!(negative, Some(("master" | "checkpoint" | "lane", at)) if at.parse::<usize>().is_ok()),
                "mode {}",
                f[3]
            );
            ensure!((f[3] != "genesis" && !f[3].starts_with("neg-genesis-")) || leaves == 0, "genesis needs N = 0");
            Ok(Spec { withdrawal, leaves, seed: f[2].parse()?, mode: f[3].to_string() })
        })
        .collect()
}

type Snapshot = Vec<(LegacyPubkey, Option<Account>)>;
struct Outcome {
    error: Option<String>,
    logs: Vec<String>,
    cu: u64,
    post: Snapshot,
}

fn main() -> Result<()> {
    ensure!(!cfg!(debug_assertions), "release build only");
    let args: Vec<String> = env::args().collect();
    ensure!(args.len() >= 6, "usage: one_tx_worst <transactions.json> <pool.so> <out.json> <specs> <label=elf.so>...");
    let all: Value = serde_json::from_slice(&fs::read(&args[1])?)?;
    let pool_elf = fs::read(&args[2])?;
    let out = Path::new(&args[3]);
    ensure!(!out.exists(), "unchanged measurement rerun forbidden: {}", out.display());
    let specs = parse_specs(&args[4])?;
    let mut elfs = vec![];
    for a in &args[5..] {
        let (label, path) = a.split_once('=').context("label=elf")?;
        let bytes = fs::read(path).with_context(|| format!("read {path}"))?;
        elfs.push((label.to_string(), path.to_string(), bytes));
    }
    let pool_id_s = all["programs"]["pool"].as_str().context("pool id")?.to_string();
    let verifier_id_s = all["programs"]["verifier"].as_str().context("verifier id")?.to_string();
    let pool_program = legacy(&pool_id_s)?;
    let verifier_program = legacy(&verifier_id_s)?;
    let find = |name: &str| all["transactions"].as_array().unwrap().iter().find(|t| t["name"] == name).cloned().ok_or_else(|| anyhow!("no transaction {name}"));

    let mut results = vec![];
    for spec in &specs {
        let op = if spec.withdrawal { "withdrawal" } else { "transfer" };
        let label = format!("{op}-N{}-seed{}-{}", spec.leaves, spec.seed, spec.mode);
        eprintln!("[{label}] building state and proving");
        let recorded = find(&format!("{op}-stage2"))?;
        let rix = &recorded["instructions"][0];
        ensure!(rix["program"] == pool_id_s.as_str(), "recorded settlement is not a Pool instruction");
        let rmetas: Vec<(LegacyPubkey, bool, bool)> = rix["accounts"].as_array().context("accounts")?.iter().map(|m| Ok((legacy(m["key"].as_str().unwrap())?, m["is_signer"].as_bool().unwrap(), m["is_writable"].as_bool().unwrap()))).collect::<Result<_>>()?;
        let expected_len = if spec.withdrawal { 17 } else { 12 };
        ensure!(rmetas.len() == expected_len, "recorded {op} has {} accounts", rmetas.len());
        let rdata = unhex(rix["data_hex"].as_str().context("data_hex")?)?;
        let recorded_request = decode_pool_v1_pair_forest_terminal_request_v1(&rdata[..rdata.len() - 4]).map_err(|e| anyhow!("recorded request: {e:?}"))?;
        let accounts = recorded_accounts(&recorded)?;
        let get = |k: &LegacyPubkey| accounts.iter().find(|(key, _)| key == k).map(|(_, a)| a.clone()).ok_or_else(|| anyhow!("recorded account {k} missing"));
        let slot = recorded["clock"]["slot"].as_u64().context("slot")?;
        // Recorded positions (same-page layout): 0 master, 1 checkpoint, 2 lane, 3 page, 4 marker,
        // 5 payer, 6 system, 7 registry, 8 entry, 9 verifier, 10 proof, [11..16 token five], last = verifier checkpoint.
        let master_key = rmetas[0].0;
        let payer_key = rmetas[5].0;
        let proof_key = rmetas[10].0;
        let vcheck_key = rmetas[rmetas.len() - 1].0;

        // Master: the recorded image with the fixture's asset id.
        let master_account = get(&master_key)?;
        let mut master = decode_pool_v1_pair_forest_master_v1(&master_account.data).map_err(|e| anyhow!("master: {e:?}"))?;
        master.identity.asset_id = M31(77);
        let master_image = encode_pool_v1_pair_forest_master_v1(&master).map_err(|e| anyhow!("master encode: {e:?}"))?.to_vec();
        ensure!(master_image.len() == master_account.data.len(), "master length");
        let domain = master.identity.deployment_domain;

        // Fixture input (pool_gate.rs): its anchor, nullifier and output lane.
        let (checkpoint_key, checkpoint_bump) = pool_v1_pair_forest_checkpoint_address(&pool_program, &master_key, CHECKPOINT_SEQUENCE);
        // Lane with N deterministic leaves.
        let mut tree = IncrementalMerkleTreeV1 { next_leaf_index: 0, root: POOL_V1_PAIR_EMPTY_ROOTS[POOL_V1_PAIR_TREE_DEPTH], frontier: core::array::from_fn(|l| POOL_V1_PAIR_EMPTY_ROOTS[l]) };
        let mut lane_roots = vec![tree.root];
        for leaf in 0..spec.leaves as u32 {
            tree = tree.append_one_with_empty_roots(strict_lane_digest(20_000 + 32 * leaf), &POOL_V1_PAIR_EMPTY_ROOTS).map_err(|e| anyhow!("append: {e:?}"))?.0;
            lane_roots.push(tree.root);
        }
        // Output lane depends on the nullifier, which the fixture fixes; derive it from a first preparation.
        let probe_snapshot = PoolV1PairLiveSnapshotV1 { pool: master_key.to_bytes(), deployment_domain: domain, sequence: tree.next_leaf_index, next_pair_index: tree.next_leaf_index, current_root: tree.root, frontier: tree.frontier };
        let probe = prepare_v7_pair_forest_transfer_fixture_v1(master_key.to_bytes(), checkpoint_key.to_bytes(), [1u8; 32], CHECKPOINT_SEQUENCE, domain, probe_snapshot).map_err(|e| anyhow!("prepare probe: {e:?}"))?;
        let nullifier = probe.public.nullifier;
        let output_lane = pool_v1_pair_forest_output_lane_v1(&nullifier).map_err(|e| anyhow!("lane: {e:?}"))?;
        let (lane_key, lane_bump) = pool_v1_pair_forest_lane_address(&pool_program, &master_key, output_lane)?;
        let lane = PoolV1PairForestLaneStateV1 { bump: lane_bump, master: master_key.to_bytes(), lane_id: output_lane, tree };
        let live_snapshot = PoolV1PairLiveSnapshotV1 { pool: master_key.to_bytes(), deployment_domain: domain, sequence: tree.next_leaf_index, next_pair_index: tree.next_leaf_index, current_root: tree.root, frontier: tree.frontier };
        let prepared = prepare_v7_pair_forest_transfer_fixture_v1(master_key.to_bytes(), checkpoint_key.to_bytes(), lane_key.to_bytes(), CHECKPOINT_SEQUENCE, domain, live_snapshot).map_err(|e| anyhow!("prepare: {e:?}"))?;
        ensure!(prepared.public.nullifier == nullifier, "nullifier depends on lane key");
        let checkpoint = PoolV1PairForestCheckpointV1 { bump: checkpoint_bump, master: master_key.to_bytes(), deployment_domain: domain, checkpoint_sequence: CHECKPOINT_SEQUENCE, global_root: prepared.public.anchor_root, lane_sequences: [0; 8] };
        let context = PoolV1PaymentRelationContextV1 {
            runtime_binding: PoolV1PaymentRuntimeBindingV1 { pool: prepared.public.pool, deployment_domain: prepared.public.deployment_domain, anchor_sequence: prepared.public.anchor_sequence, anchor_root: prepared.public.anchor_root, asset_id: prepared.public.asset_id },
            spent_nullifiers: &[],
        };
        let (payment, statement, compiled) = if spec.withdrawal {
            let change = PoolV1OutputNoteWitnessV1 { owner_key: digest(700), salt: digest(800), value: 750 };
            let public = PoolV1WithdrawalPublicV1 {
                pool: prepared.public.pool,
                deployment_domain: prepared.public.deployment_domain,
                anchor_sequence: prepared.public.anchor_sequence,
                anchor_root: prepared.public.anchor_root,
                nullifier: prepared.public.nullifier,
                asset_id: prepared.public.asset_id,
                amount: WITHDRAWAL_AMOUNT,
                destination_token_account: DESTINATION_TOKEN_ACCOUNT_BYTES,
                change_commitment: pool_v1_note_commitment(&change.owner_key, change.value, prepared.public.asset_id, &change.salt),
            };
            let witness = PoolV1PairForestWithdrawalWitnessV1 { input: prepared.witness.input, change };
            let compiled = compile_pool_v1_pair_forest_withdrawal_merged_c1_v1(&public, &witness, context, live_snapshot).map_err(|e| anyhow!("compile withdrawal: {e:?}"))?;
            let mut common = *prepared.statement.common();
            common.lane_transition = compiled.public_statement;
            (PoolV1PairForestTerminalPaymentV1::Withdrawal(public), PoolV1PairForestTerminalStatementV1::Withdrawal { common, public }, compiled)
        } else {
            let compiled = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&prepared.public, &prepared.witness, context, live_snapshot).map_err(|e| anyhow!("compile transfer: {e:?}"))?;
            (PoolV1PairForestTerminalPaymentV1::PrivateTransfer(prepared.public), prepared.statement.clone(), compiled)
        };
        let afterstate = compiled.public_statement.candidate_afterstate;
        let request = PoolV1PairForestTerminalRequestV1 { verifier_profile: recorded_request.verifier_profile, verifier_release: recorded_request.verifier_release, pool_program: pool_program.to_bytes(), public: payment };
        let request_bytes = encode_pool_v1_pair_forest_terminal_request_v1(&request).map_err(|e| anyhow!("request: {e:?}"))?.to_vec();
        let hints = pool_v1_pair_forest_terminal_bump_hints_v1(&pool_program, &master_key, &lane_key, lane.tree.next_leaf_index, spec.withdrawal);
        let ix_data = encode_pair_forest_terminal_instruction_data_v1(&request_bytes, hints);

        // Prove (deterministic fixture seed), re-pack, verify on the host and read the query set.
        let t0 = Instant::now();
        let (pinned, _) = prover::prove_masked_fixture(statement_public(&statement), &compiled, Variant::S2, HOST_HASH, &[spec.seed; 32]).map_err(|e| anyhow!("prove: {e:?}"))?;
        let prove_seconds = t0.elapsed().as_secs_f64();
        let packed = one_tx::pack(statement.semantic_public(), &pinned, Sha).map_err(|e| anyhow!("re-pack: {e:?}"))?;
        let _ = aspis_r1_cost_probe::trace::take();
        one_tx::verify(statement.semantic_public(), &packed, Sha, None).map_err(|e| anyhow!("host verify: {e:?}"))?;
        let trace = aspis_r1_cost_probe::trace::take();
        let mut queries = [u32::MAX; 22];
        for (tag, i, bytes) in &trace {
            if *tag == 5 && *i < 22 {
                queries[*i] = u32::from_le_bytes(bytes[..4].try_into().unwrap());
            }
        }
        ensure!(queries.iter().all(|&q| q < 1 << 18), "query trace incomplete");
        let mut c = queries.to_vec();
        c.sort_unstable();
        c.dedup();
        ensure!(c.len() == 22, "queries not distinct");
        let mut f: Vec<u32> = queries.iter().map(|q| q / 4).collect();
        f.sort_unstable();
        f.dedup();
        let nodes = [multiproof::node_count_merged(&c).unwrap(), multiproof::node_count_merged(&c).unwrap(), multiproof::node_count_merged(&f).unwrap()];
        let slot_nonzero: Vec<usize> = (0..3).map(|t| packed[one_tx::format::slot_offset(t)..one_tx::format::slot_offset(t + 1)].chunks(32).filter(|b| b.iter().any(|x| *x != 0)).count()).collect();
        ensure!(slot_nonzero == nodes.to_vec(), "node count {nodes:?} differs from nonzero slot blocks {slot_nonzero:?}");
        let total_nodes: usize = nodes.iter().sum();
        let parents = total_nodes + 22 + 22 + f.len() - 3;
        let swaps = [insertion_swaps(&queries, false), insertion_swaps(&queries, true)];

        let mut buffer = encode_pool_v1_pair_verified_afterstate_v1(&afterstate).map_err(|e| anyhow!("afterstate: {e:?}"))?.to_vec();
        ensure!(buffer.len() == POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, "afterstate length");
        buffer.extend_from_slice(&packed);

        // History pages.
        let current = root_history_location(lane.tree.next_leaf_index);
        let next = root_history_location(lane.tree.next_leaf_index + 1);
        let rollover = current.page_number != next.page_number;
        let genesis = spec.mode == "genesis" || spec.mode.starts_with("neg-genesis-");
        let negative = spec.mode.strip_prefix("neg-").and_then(|r| r.split_once('-'));
        let page_key = pool_v1_root_page_address(&pool_program, &lane_key, current.page_number).0;
        let next_page_key = pool_v1_root_page_address(&pool_program, &lane_key, next.page_number).0;
        let mut page_image = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        if !genesis {
            let first = (current.page_number * POOL_V1_ROOT_HISTORY_CAPACITY as u64) as usize;
            initialize_root_history_page_bytes_v1(&mut page_image, lane_key.to_bytes(), current.page_number, &lane_roots[first..]).map_err(|e| anyhow!("page: {e:?}"))?;
        }
        // Expected images after a successful settlement.
        let mut expected_page = page_image.clone();
        let mut expected_next_page = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        // Pre-state of the next page at rollover (zero unless a negative scenario plants a byte).
        let mut next_page_image = vec![0u8; POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES];
        if genesis {
            initialize_root_history_page_bytes_v1(&mut expected_page, lane_key.to_bytes(), 0, &[lane.tree.root, afterstate.next_root]).map_err(|e| anyhow!("genesis page: {e:?}"))?;
        } else if rollover {
            initialize_root_history_page_bytes_v1(&mut expected_next_page, lane_key.to_bytes(), next.page_number, &[afterstate.next_root]).map_err(|e| anyhow!("rollover page: {e:?}"))?;
        } else {
            append_root_history_page_bytes_v1(&mut expected_page, afterstate.next_pair_index, afterstate.next_root).map_err(|e| anyhow!("append page: {e:?}"))?;
        }
        // Negative scenarios: plant one non-zero byte where the Pool requires zero bytes.
        let mut planted: Option<(&str, usize)> = None;
        let mut master_run_image = master_image.clone();
        let mut checkpoint_image = encode_pool_v1_pair_forest_checkpoint_v1(&checkpoint).map_err(|e| anyhow!("{e:?}"))?.to_vec();
        let mut lane_image = encode_pool_v1_pair_forest_lane_state_v1(&lane, &POOL_V1_PAIR_EMPTY_ROOTS).map_err(|e| anyhow!("{e:?}"))?.to_vec();
        if let Some((place @ ("master" | "checkpoint" | "lane"), at)) = negative {
            let position: usize = at.parse()?;
            let image = match place {
                "master" => &mut master_run_image,
                "checkpoint" => &mut checkpoint_image,
                _ => &mut lane_image,
            };
            ensure!(position < image.len(), "{place} offset {position} beyond {} bytes", image.len());
            image[position] ^= 0x01;
            planted = Some((place, position));
        } else if let Some((place, at)) = negative {
            let page_len = POOL_V1_ROOT_HISTORY_PAGE_ACCOUNT_BYTES;
            let region_start = match place {
                "tail" => {
                    ensure!(!genesis && !rollover, "neg-tail needs a same-page position (N mod 256 != 255)");
                    64 + 32 * (current.slot as usize + 1)
                }
                "next" => {
                    ensure!(rollover, "neg-next needs a rollover position (N mod 256 = 255)");
                    0
                }
                _ => 0,
            };
            let position = match at {
                "first" => region_start,
                "mid" => (region_start + page_len - 1) / 2,
                _ => page_len - 1,
            };
            let image = if place == "next" { &mut next_page_image } else { &mut page_image };
            ensure!(image[position] == 0, "planted position {position} is not zero before planting");
            image[position] = 0x01;
            planted = Some((if place == "next" { "next_page" } else { "current_page" }, position));
        }
        let next_lane = PoolV1PairForestLaneStateV1 { tree: IncrementalMerkleTreeV1 { next_leaf_index: afterstate.next_pair_index, root: afterstate.next_root, frontier: afterstate.next_frontier }, ..lane };
        let expected_lane = encode_pool_v1_pair_forest_lane_state_v1(&next_lane, &POOL_V1_PAIR_EMPTY_ROOTS).map_err(|e| anyhow!("lane encode: {e:?}"))?.to_vec();
        let marker_key = pool_v1_pair_forest_nullifier_marker_address(&pool_program, &master_key, &encode_digest_canonical(&nullifier)).map_err(|e| anyhow!("marker: {e:?}"))?.0;
        let destination_key = LegacyPubkey::new_from_array(DESTINATION_TOKEN_ACCOUNT_BYTES);

        // Account list.
        let mut metas = vec![
            AccountMeta::new_readonly(addr(&master_key), false),
            AccountMeta::new_readonly(addr(&checkpoint_key), false),
            AccountMeta::new(addr(&lane_key), false),
        ];
        if rollover {
            metas.push(AccountMeta::new_readonly(addr(&page_key), false));
            metas.push(AccountMeta::new(addr(&next_page_key), false));
        } else {
            metas.push(AccountMeta::new(addr(&page_key), false));
        }
        metas.push(AccountMeta::new(addr(&marker_key), false));
        for (i, (key, signer, writable)) in rmetas.iter().enumerate().skip(5) {
            let key = if spec.withdrawal && i == 13 { destination_key } else { *key };
            metas.push(if *writable { AccountMeta::new(addr(&key), *signer) } else { AccountMeta::new_readonly(addr(&key), *signer) });
        }
        let instruction = Instruction { program_id: addr(&pool_program), accounts: metas.clone(), data: ix_data.clone() };
        let watched: Vec<LegacyPubkey> = metas.iter().map(|m| LegacyPubkey::new_from_array(m.pubkey.to_bytes())).filter(|k| *k != legacy(SYSTEM).unwrap()).collect();

        let marker_rent = rent_for(aspis_statement::pool_v1::POOL_V1_NULLIFIER_MARKER_ACCOUNT_BYTES);
        let run = |elf: &[u8], marker_prefund: Option<u64>, cu_limit: u32| -> Result<(Outcome, Snapshot)> {
            let mut svm = LiteSVM::new().with_sigverify(false);
            svm.warp_to_slot(slot);
            let mut rent = Vec::with_capacity(17);
            rent.extend_from_slice(&2_540u64.to_le_bytes());
            rent.extend_from_slice(&2.0f64.to_le_bytes());
            rent.push(50);
            svm.set_account(addr(&legacy("SysvarRent111111111111111111111111111111111")?), Account { lamports: 1_009_200, data: rent, owner: addr(&legacy("Sysvar1111111111111111111111111111111111111")?), executable: false, rent_epoch: u64::MAX }).map_err(|e| anyhow!("rent: {e:?}"))?;
            svm.add_program(addr(&pool_program), &pool_elf).map_err(|e| anyhow!("pool: {e:?}"))?;
            svm.add_program(addr(&verifier_program), elf).map_err(|e| anyhow!("verifier: {e:?}"))?;
            for (k, a) in &accounts {
                svm.set_account(addr(k), a.clone()).map_err(|e| anyhow!("set: {e:?}"))?;
            }
            let pool_owned = |data: Vec<u8>| Account { lamports: rent_for(data.len()), data, owner: addr(&pool_program), executable: false, rent_epoch: u64::MAX };
            svm.set_account(addr(&master_key), Account { data: master_run_image.clone(), ..master_account.clone() }).map_err(|e| anyhow!("{e:?}"))?;
            svm.set_account(addr(&checkpoint_key), pool_owned(checkpoint_image.clone())).map_err(|e| anyhow!("{e:?}"))?;
            svm.set_account(addr(&lane_key), pool_owned(lane_image.clone())).map_err(|e| anyhow!("{e:?}"))?;
            svm.set_account(addr(&page_key), pool_owned(page_image.clone())).map_err(|e| anyhow!("{e:?}"))?;
            if rollover {
                svm.set_account(addr(&next_page_key), pool_owned(next_page_image.clone())).map_err(|e| anyhow!("{e:?}"))?;
            }
            let proof_account = get(&proof_key)?;
            svm.set_account(addr(&proof_key), Account { lamports: rent_for(buffer.len()), data: buffer.clone(), ..proof_account }).map_err(|e| anyhow!("{e:?}"))?;
            if spec.withdrawal {
                let recorded_destination = get(&rmetas[13].0)?;
                svm.set_account(addr(&destination_key), recorded_destination).map_err(|e| anyhow!("{e:?}"))?;
            }
            if let Some(lamports) = marker_prefund {
                svm.set_account(addr(&marker_key), Account { lamports, data: vec![], owner: addr(&legacy(SYSTEM)?), executable: false, rent_epoch: u64::MAX }).map_err(|e| anyhow!("{e:?}"))?;
            }
            let pre: Snapshot = watched.iter().map(|k| (*k, svm.get_account(&addr(k)))).collect();
            let ixs = [ComputeBudgetInstruction::set_compute_unit_limit(cu_limit), ComputeBudgetInstruction::request_heap_frame(256 * 1024), instruction.clone()];
            let message = Message::new_with_blockhash(&ixs, Some(&addr(&payer_key)), &svm.latest_blockhash());
            let (error, meta) = match svm.send_transaction(Transaction::new_unsigned(message)) {
                Ok(m) => (None, m),
                Err(e) => (Some(format!("{:?}", e.err)), e.meta),
            };
            let post: Snapshot = watched.iter().map(|k| (*k, svm.get_account(&addr(k)))).collect();
            Ok((Outcome { error, logs: meta.logs, cu: meta.compute_units_consumed, post }, pre))
        };
        let data_of = |s: &Snapshot, k: &LegacyPubkey| s.iter().find(|(key, _)| key == k).and_then(|(_, a)| a.as_ref()).map(|a| a.data.clone());
        let token_amount = |s: &Snapshot, k: &LegacyPubkey| data_of(s, k).filter(|d| d.len() == 165).map(|d| u64::from_le_bytes(d[64..72].try_into().unwrap()));
        let vault_key = if spec.withdrawal { rmetas[12].0 } else { LegacyPubkey::default() };
        let check_success = |o: &Outcome, pre: &Snapshot| -> Value {
            let lane_ok = data_of(&o.post, &lane_key) == Some(expected_lane.clone());
            let page_ok = data_of(&o.post, &page_key) == Some(expected_page.clone());
            let next_ok = !rollover || data_of(&o.post, &next_page_key) == Some(expected_next_page.clone());
            let marker_ok = o.post.iter().find(|(k, _)| *k == marker_key).and_then(|(_, a)| a.as_ref()).map(|a| a.owner == addr(&pool_program) && a.data.iter().any(|b| *b != 0)) == Some(true);
            let token_ok = !spec.withdrawal
                || (token_amount(&o.post, &destination_key) == token_amount(pre, &destination_key).map(|x| x + u64::from(WITHDRAWAL_AMOUNT))
                    && token_amount(&o.post, &vault_key) == token_amount(pre, &vault_key).map(|x| x - u64::from(WITHDRAWAL_AMOUNT)));
            json!({"lane": lane_ok, "page": page_ok, "next_page": next_ok, "marker": marker_ok, "tokens": token_ok, "all": lane_ok && page_ok && next_ok && marker_ok && token_ok})
        };
        let unchanged_but_fee = |o: &Outcome, pre: &Snapshot| -> bool {
            pre.iter().zip(o.post.iter()).all(|((k, a), (_, b))| {
                let norm = |x: &Option<Account>| x.as_ref().filter(|a| a.lamports > 0 || !a.data.is_empty()).map(|a| (if *k == payer_key { 0 } else { a.lamports }, a.owner, a.data.clone()));
                norm(a) == norm(b)
            })
        };

        let state_hash = |s: &Snapshot| -> String {
            let mut h = Sha256::new();
            for (k, a) in s {
                h.update(k.to_bytes());
                match a {
                    Some(a) => {
                        h.update([1u8]);
                        h.update(a.lamports.to_le_bytes());
                        h.update(a.owner.to_bytes());
                        h.update([u8::from(a.executable)]);
                        h.update((a.data.len() as u64).to_le_bytes());
                        h.update(&a.data);
                    }
                    None => h.update([0u8]),
                }
            }
            format!("{:x}", h.finalize())
        };
        let mut elf_results = vec![];
        for (elabel, epath, elf) in &elfs {
            let mut runs = vec![];
            if negative.is_some() {
                let (o, pre) = run(elf, None, 1_400_000)?;
                eprintln!("[{label}] {elabel} negative: {} CU, error {:?}", o.cu, o.error);
                let unchanged = unchanged_but_fee(&o, &pre);
                runs.push(json!({"variant": "negative-marker-absent", "planted": planted.map(|(page, position)| json!({"page": page, "position": position, "value_or_xor": 1})), "error": o.error, "transaction_cu": o.cu, "pool_cu": consumed(&o.logs, &pool_id_s), "verifier_cu": consumed(&o.logs, &verifier_id_s), "rejected": o.error.is_some(), "unchanged_except_payer_fee": unchanged, "post_state_sha256": state_hash(&o.post), "pre_state_sha256": state_hash(&pre), "logs": o.logs}));
                elf_results.push(json!({"elf": elabel, "path": epath, "elf_sha256": sha(elf), "runs": runs}));
                continue;
            }
            let variants: Vec<(&str, Option<u64>)> = if spec.mode == "basic" { vec![("marker-absent", None)] } else { vec![("marker-absent", None), ("marker-one-lamport", Some(1)), ("marker-full-rent", Some(marker_rent))] };
            let mut absent_cu = None;
            for (vname, prefund) in variants {
                let (o, pre) = run(elf, prefund, 1_400_000)?;
                if vname == "marker-absent" {
                    absent_cu = Some(o.cu);
                }
                eprintln!("[{label}] {elabel} {vname}: {} CU, error {:?}", o.cu, o.error);
                runs.push(json!({"variant": vname, "error": o.error, "transaction_cu": o.cu, "pool_cu": consumed(&o.logs, &pool_id_s), "verifier_cu": consumed(&o.logs, &verifier_id_s), "state": check_success(&o, &pre), "post_state_sha256": state_hash(&o.post), "logs": o.logs}));
            }
            if spec.mode != "basic" {
                // One unit below the measured cost: the transaction must fail and change nothing but the fee.
                let limit = (absent_cu.unwrap() - 1) as u32;
                let (o, pre) = run(elf, None, limit)?;
                runs.push(json!({"variant": "marker-absent-limit-one-below", "cu_limit": limit, "error": o.error, "transaction_cu": o.cu, "unchanged_except_payer_fee": unchanged_but_fee(&o, &pre), "post_state_sha256": state_hash(&o.post), "log_tail": o.logs.iter().rev().take(4).collect::<Vec<_>>()}));
            }
            elf_results.push(json!({"elf": elabel, "path": epath, "elf_sha256": sha(elf), "runs": runs}));
        }
        results.push(json!({
            "scenario": label, "operation": op, "lane_leaves_before": spec.leaves, "seed": spec.seed, "mode": spec.mode,
            "page_path": if genesis { "genesis" } else if rollover { "rollover" } else { "same-page" },
            "planted": planted.map(|(page, position)| json!({"page": page, "position": position})),
            "current_page": {"number": current.page_number, "filled_before": if genesis { 0 } else { current.slot as u64 + 1 }},
            "account_count": metas.len(), "prove_seconds": prove_seconds,
            "pinned_proof_sha256": sha(&pinned), "summed_proof_sha256": sha(&packed),
            "queries": queries.to_vec(), "nodes": nodes.to_vec(), "nodes_total": total_nodes, "folded_distinct": f.len(),
            "merkle_parent_digests": parents, "insertion_swaps": swaps.to_vec(),
            "elfs": elf_results,
        }));
        // Write after every scenario so a timeout keeps what was measured.
        let value = json!({
            "label": "ASPIS WORST-CASE COMPUTE PROBE. Measurements in LiteSVM 0.16.0 (agave 4.2.1), signature verification off, 256 KiB heap; fixture witness; not proofs",
            "source_revision": env::var("ASPIS_SOURCE_REVISION").unwrap_or_default(),
            "pool_elf_sha256": sha(&pool_elf), "transactions_sha256": sha(&fs::read(&args[1])?),
            "specs": args[4], "results": results,
        });
        let tmp = out.with_extension("partial");
        fs::write(&tmp, serde_json::to_string_pretty(&value)? + "\n")?;
    }
    fs::rename(out.with_extension("partial"), out)?;
    Ok(())
}
