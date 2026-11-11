//! FUTURE-VERSION EXPERIMENT. Replays a RECORDED devnet settlement transaction
//! (PIN2 run of 11 November 2026) in LiteSVM from its recorded pre-state, at the
//! real 1,400,000 CU limit:
//!
//! - control: the deployed verifier ELF and the recorded accounts; the Pool's
//!   compute units must equal the recorded ones, which validates the replay;
//! - one transaction: the one-transaction verifier ELF at the same address,
//!   with the recorded proof re-packed into the summed format (one multiproof
//!   per tree and the stage D certificate inside the proof, computed here from
//!   public data) in the proof buffer. Stage 1 never runs; this single
//!   transaction verifies the whole proof and settles.
//!
//! Signature verification is off (the recorded payer's key is not available);
//! nothing else about the transaction or the accounts is changed.
//!
//! usage: one_tx_replay <transactions.json> <pool.so> <verifier-deployed.so>
//!        <verifier-one-tx.so> <transfer|withdrawal> <out.json>
use anyhow::{anyhow, ensure, Context, Result};
use litesvm::LiteSVM;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{account_meta::AccountMeta, Instruction};
use solana_message::Message;
use solana_program::pubkey::Pubkey as LegacyPubkey;
use solana_transaction::Transaction;
use std::{env, fs, path::Path, str::FromStr};

fn sha(b: &[u8]) -> String {
    format!("{:x}", Sha256::digest(b))
}
fn address(s: &str) -> Result<Address> {
    Ok(Address::new_from_array(LegacyPubkey::from_str(s).map_err(|e| anyhow!("key {s}: {e:?}"))?.to_bytes()))
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
struct Recorded {
    key: Address,
    account: Account,
}
fn recorded_accounts(tx: &Value) -> Result<Vec<Recorded>> {
    let mut out = vec![];
    for a in tx["pre"]["accounts"].as_array().context("pre.accounts")? {
        if !a["exists"].as_bool().unwrap_or(false) || a["executable"].as_bool().unwrap_or(false) {
            continue;
        }
        let data = unbase64(a["data_base64"].as_str().context("data")?)?;
        ensure!(data.len() as u64 == a["space"].as_u64().context("space")?, "recorded data length");
        out.push(Recorded {
            key: address(a["key"].as_str().context("key")?)?,
            account: Account { lamports: a["lamports"].as_u64().context("lamports")?, data, owner: address(a["owner"].as_str().context("owner")?)?, executable: false, rent_epoch: u64::MAX },
        });
    }
    Ok(out)
}
/// (lamports, owner, data) of one account after a run, or `None` if absent.
type State = Vec<(String, Option<(u64, String, Vec<u8>)>)>;
struct Outcome {
    error: Option<String>,
    logs: Vec<String>,
    transaction_cu: u64,
    post: State,
}
fn base58(a: &Address) -> String {
    LegacyPubkey::new_from_array(a.to_bytes()).to_string()
}
/// The recorded state of every non-executable account of a recorded snapshot.
fn recorded_state(snapshot: &Value) -> Result<State> {
    let mut out = vec![];
    for a in snapshot["accounts"].as_array().context("accounts")? {
        if a["executable"].as_bool().unwrap_or(false) {
            continue;
        }
        let key = a["key"].as_str().context("key")?.to_string();
        if !a["exists"].as_bool().unwrap_or(false) {
            out.push((key, None));
            continue;
        }
        out.push((key, Some((a["lamports"].as_u64().context("lamports")?, a["owner"].as_str().context("owner")?.to_string(), unbase64(a["data_base64"].as_str().context("data")?)?))));
    }
    Ok(out)
}
/// Keys whose state differs between two snapshots, ignoring `skip`; lamports are
/// compared only for keys outside `skip_lamports`.
fn differing(a: &State, b: &State, skip: &[&str], skip_lamports: &[&str]) -> Vec<String> {
    let mut out = vec![];
    for (key, left) in a {
        if skip.contains(&key.as_str()) {
            continue;
        }
        let right = b.iter().find(|(k, _)| k == key).map(|(_, v)| v);
        let same = match (left, right) {
            (None, Some(None)) => true,
            (Some(l), Some(Some(r))) => l.1 == r.1 && l.2 == r.2 && (skip_lamports.contains(&key.as_str()) || l.0 == r.0),
            _ => false,
        };
        if !same {
            out.push(key.clone());
        }
    }
    out
}
fn consumed(logs: &[String], program: &str) -> Option<u64> {
    logs.iter().rev().find_map(|l| l.strip_prefix(&format!("Program {program} consumed "))?.split_whitespace().next()?.parse().ok())
}
fn main() -> Result<()> {
    ensure!(!cfg!(debug_assertions), "release build only");
    let args: Vec<_> = env::args().collect();
    ensure!(args.len() == 7, "usage: one_tx_replay <transactions.json> <pool.so> <verifier-deployed.so> <verifier-one-tx.so> <transfer|withdrawal> <out.json>");
    let all: Value = serde_json::from_slice(&fs::read(&args[1])?)?;
    let pool_elf = fs::read(&args[2])?;
    let deployed_elf = fs::read(&args[3])?;
    let one_tx_elf = fs::read(&args[4])?;
    let operation = &args[5];
    let out = Path::new(&args[6]);
    ensure!(!out.exists(), "unchanged measurement rerun forbidden: {}", out.display());
    let pool_id = all["programs"]["pool"].as_str().context("pool id")?.to_string();
    let verifier_id = all["programs"]["verifier"].as_str().context("verifier id")?.to_string();
    let upload_id = all["upload_program"].as_str().context("upload id")?.to_string();
    let find = |name: String| all["transactions"].as_array().unwrap().iter().find(|t| t["name"] == name.as_str()).cloned().ok_or_else(|| anyhow!("no transaction {name}"));
    let stage1 = find(format!("{operation}-stage1"))?;
    let stage2 = find(format!("{operation}-stage2"))?;
    ensure!(stage2["instructions"].as_array().map(|a| a.len()) == Some(1), "one recorded instruction expected");
    let recorded_ix = &stage2["instructions"][0];
    ensure!(recorded_ix["program"] == pool_id.as_str(), "recorded settlement is not a Pool instruction");
    let payer = address(stage2["keys"][0].as_str().context("payer")?)?;
    let instruction = Instruction {
        program_id: address(&pool_id)?,
        accounts: recorded_ix["accounts"].as_array().context("accounts")?.iter().map(|m| {
            let key = address(m["key"].as_str().unwrap())?;
            let signer = m["is_signer"].as_bool().unwrap();
            Ok(if m["is_writable"].as_bool().unwrap() { AccountMeta::new(key, signer) } else { AccountMeta::new_readonly(key, signer) })
        }).collect::<Result<Vec<_>>>()?,
        data: unhex(recorded_ix["data_hex"].as_str().context("data_hex")?)?,
    };
    let slot = stage2["clock"]["slot"].as_u64().context("slot")?;
    let accounts2 = recorded_accounts(&stage2)?;
    let accounts1 = recorded_accounts(&stage1)?;
    let upload = address(&upload_id)?;
    let verifier = address(&verifier_id)?;
    let proof = accounts2.iter().find(|a| a.account.owner == upload && a.account.data.len() > 50_000).context("proof buffer")?;
    let public = accounts1.iter().find(|a| a.account.owner == upload && a.account.data.len() == 1880).context("public statement")?;
    let checkpoint = accounts2.iter().find(|a| a.account.owner == verifier && a.account.data.len() == 1768).context("verifier account")?;
    let prefix = aspis_statement::pool_v1::POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let statement = aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(&public.account.data).map_err(|e| anyhow!("statement: {e:?}"))?;
    // The recorded proof re-packed into the summed format, behind the recorded candidate prefix.
    let packed = aspis_r1_cost_probe::verifier::candidate::fused::to_summed_format(statement.semantic_public(), &proof.account.data[prefix..], Sha).map_err(|e| anyhow!("re-pack: {e:?}"))?;
    let mut buffer = proof.account.data[..prefix].to_vec();
    buffer.extend_from_slice(&packed);

    let pre_state = recorded_state(&stage2["pre"])?;
    let recorded_post = recorded_state(&stage2["post"])?;
    let run_with = |verifier_elf: &[u8], proof_buffer: Option<Vec<u8>>, marker_prefund: Option<(Address, u64)>| -> Result<Outcome> {
        let mut svm = LiteSVM::new().with_sigverify(false);
        svm.warp_to_slot(slot);
        svm.add_program(address(&pool_id)?, &pool_elf).map_err(|e| anyhow!("load pool: {e:?}"))?;
        svm.add_program(verifier, verifier_elf).map_err(|e| anyhow!("load verifier: {e:?}"))?;
        for a in &accounts2 {
            let mut account = a.account.clone();
            if a.key == proof.key {
                if let Some(data) = &proof_buffer {
                    account.data = data.clone();
                }
            }
            svm.set_account(a.key, account).map_err(|e| anyhow!("set account: {e:?}"))?;
        }
        if let Some((marker, lamports)) = marker_prefund {
            // A marker address funded in advance by a third party: system-owned, no data.
            svm.set_account(marker, Account { lamports, data: vec![], owner: address("11111111111111111111111111111111")?, executable: false, rent_epoch: u64::MAX }).map_err(|e| anyhow!("prefund: {e:?}"))?;
        }
        let instructions = [ComputeBudgetInstruction::set_compute_unit_limit(1_400_000), ComputeBudgetInstruction::request_heap_frame(256 * 1024), instruction.clone()];
        let message = Message::new_with_blockhash(&instructions, Some(&payer), &svm.latest_blockhash());
        let tx = Transaction::new_unsigned(message);
        let (error, meta) = match svm.send_transaction(tx) {
            Ok(m) => (None, m),
            Err(e) => (Some(format!("{:?}", e.err)), e.meta),
        };
        let mut post = vec![];
        for (key, _) in &pre_state {
            let account = svm.get_account(&address(key)?);
            post.push((key.clone(), account.filter(|a| a.lamports > 0 || !a.data.is_empty()).map(|a| (a.lamports, base58(&a.owner), a.data))));
        }
        Ok(Outcome { error, logs: meta.logs, transaction_cu: meta.compute_units_consumed, post })
    };
    let run = |verifier_elf: &[u8], proof_buffer: Option<Vec<u8>>| run_with(verifier_elf, proof_buffer, None);
    let record = |name: &str, o: &Outcome| json!({"mode": name, "error": o.error, "transaction_cu": o.transaction_cu, "pool_cu": consumed(&o.logs, &pool_id), "verifier_cu": consumed(&o.logs, &verifier_id), "logs": o.logs});

    // Control: the deployed verifier on the recorded accounts.
    let control = run(&deployed_elf, None)?;
    let recorded_pool = consumed(&stage2["meta"]["logMessages"].as_array().unwrap().iter().map(|l| l.as_str().unwrap().to_string()).collect::<Vec<_>>(), &pool_id);
    let control_ok = control.error.is_none() && consumed(&control.logs, &pool_id) == recorded_pool;
    // One transaction: the summed-format proof buffer; the seventh account is left as recorded and is not read.
    let _ = checkpoint;
    let one = run(&one_tx_elf, Some(buffer.clone()))?;
    // Negatives: one changed certificate byte; the recorded pinned-format buffer.
    let mut bad = buffer.clone();
    let last = bad.len() - 9;
    bad[last] ^= 1;
    let changed = run(&one_tx_elf, Some(bad))?;
    let stale = run(&one_tx_elf, None)?;
    // Final account states. The replayed transaction is unsigned and built as a legacy message, so the
    // payer's balance differs from the recorded one by the fee; everything else must match.
    let payer_key = stage2["keys"][0].as_str().unwrap().to_string();
    let proof_key = base58(&proof.key);
    let control_vs_recorded = differing(&control.post, &recorded_post, &[], &[payer_key.as_str()]);
    // One transaction against the control: every account except the proof buffer (different bytes by
    // design, and not written by either run), including the payer's balance.
    let one_vs_control = differing(&one.post, &control.post, &[proof_key.as_str()], &[]);
    let one_proof_untouched = one.post.iter().find(|(k, _)| *k == proof_key).and_then(|(_, v)| v.as_ref()).map(|v| v.2 == buffer) == Some(true);
    // Rejected runs leave every account as it was before the transaction (the failed
    // transaction is not committed, so the payer is unchanged too), apart from the proof buffer we installed.
    let changed_vs_pre = differing(&changed.post, &pre_state, &[proof_key.as_str()], &[]);
    let stale_vs_pre = differing(&stale.post, &pre_state, &[], &[]);
    // Marker funding states of the Pool (one, three and two System calls): the marker is the
    // account absent before and Pool-owned after the recorded settlement.
    let marker = recorded_post.iter().find(|(k, v)| v.as_ref().map(|v| v.1 == pool_id) == Some(true) && pre_state.iter().any(|(pk, pv)| pk == k && pv.is_none())).context("marker")?;
    let marker_rent = marker.1.as_ref().unwrap().0;
    let marker_address = address(&marker.0)?;
    let partial = run_with(&one_tx_elf, Some(buffer.clone()), Some((marker_address, 1)))?;
    let funded = run_with(&one_tx_elf, Some(buffer.clone()), Some((marker_address, marker_rent)))?;
    let variant_state_ok = |o: &Outcome| differing(&o.post, &control.post, &[proof_key.as_str()], &[payer_key.as_str()]).is_empty();
    let summary = json!({
        "operation": operation,
        "recorded_pool_cu": recorded_pool,
        "control_pool_cu": consumed(&control.logs, &pool_id),
        "control_reproduces_recorded": control_ok,
        "one_tx_error": one.error,
        "one_tx_pool_cu": consumed(&one.logs, &pool_id),
        "one_tx_verifier_cu": consumed(&one.logs, &verifier_id),
        "one_tx_transaction_cu": one.transaction_cu,
        "one_tx_completes_at_1400000": one.error.is_none(),
        "changed_certificate_rejected": changed.error.is_some(),
        "pinned_format_buffer_rejected": stale.error.is_some(),
        "control_final_state_equals_recorded_except_payer_fee": control_vs_recorded.is_empty(),
        "one_tx_final_state_equals_control": one_vs_control.is_empty() && one_proof_untouched,
        "rejected_runs_leave_state_unchanged": changed_vs_pre.is_empty() && stale_vs_pre.is_empty(),
        "state_differences": {"control_vs_recorded": control_vs_recorded, "one_tx_vs_control": one_vs_control, "changed_vs_pre": changed_vs_pre, "pinned_vs_pre": stale_vs_pre},
        "marker_prefunded_one_lamport": {"error": partial.error, "transaction_cu": partial.transaction_cu, "pool_cu": consumed(&partial.logs, &pool_id), "final_state_equals_control_except_payer": variant_state_ok(&partial)},
        "marker_prefunded_full_rent": {"error": funded.error, "transaction_cu": funded.transaction_cu, "pool_cu": consumed(&funded.logs, &pool_id), "final_state_equals_control_except_payer": variant_state_ok(&funded)},
        "proof_buffer_bytes": buffer.len(),
    });
    println!("{summary}");
    let value = json!({
        "label": "FUTURE-VERSION EXPERIMENT — UNPROVED. Replay of a recorded devnet settlement in LiteSVM, signature verification off, real 1,400,000 CU limit",
        "source_revision": env::var("ASPIS_SOURCE_REVISION")?,
        "pool_elf_sha256": sha(&pool_elf), "deployed_verifier_elf_sha256": sha(&deployed_elf), "one_tx_verifier_elf_sha256": sha(&one_tx_elf),
        "recorded_signature": stage2["signature"], "recorded_slot": slot, "summed_proof_sha256": sha(&packed),
        "runtime": {"litesvm": "0.16.0", "agave": "4.2.1", "heap_bytes": 262144},
        "summary": summary,
        "runs": [record("control-deployed-verifier", &control), record("one-transaction", &one), record("one-transaction-changed-certificate", &changed), record("one-transaction-pinned-format-buffer", &stale), record("one-transaction-marker-prefunded-one-lamport", &partial), record("one-transaction-marker-prefunded-full-rent", &funded)],
    });
    fs::write(out, serde_json::to_string_pretty(&value)? + "\n")?;
    ensure!(control_ok, "control did not reproduce the recorded compute units");
    ensure!(control_vs_recorded.is_empty(), "control final state differs from the recorded one: {control_vs_recorded:?}");
    Ok(())
}
