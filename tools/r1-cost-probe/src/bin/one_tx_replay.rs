//! FUTURE-VERSION EXPERIMENT. Replays a RECORDED devnet settlement transaction
//! (PIN2 run of 11 November 2026) in LiteSVM from its recorded pre-state, at the
//! real 1,400,000 CU limit:
//!
//! - control: the deployed verifier ELF and the recorded accounts; the Pool's
//!   compute units must equal the recorded ones, which validates the replay;
//! - one transaction: the one-transaction verifier ELF at the same address,
//!   with the stage D certificate (computed here from the public proof data)
//!   placed at the start of the verifier-owned seventh account. Stage 1 never
//!   runs; this single transaction verifies the whole proof and settles.
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
struct Outcome {
    error: Option<String>,
    logs: Vec<String>,
    transaction_cu: u64,
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
    let certificate = aspis_r1_cost_probe::verifier::candidate::fused::final_message_certificate(statement.semantic_public(), &proof.account.data[prefix..], Sha).map_err(|e| anyhow!("certificate: {e:?}"))?;

    let run = |verifier_elf: &[u8], seventh: Option<Vec<u8>>| -> Result<Outcome> {
        let mut svm = LiteSVM::new().with_sigverify(false);
        svm.warp_to_slot(slot);
        svm.add_program(address(&pool_id)?, &pool_elf).map_err(|e| anyhow!("load pool: {e:?}"))?;
        svm.add_program(verifier, verifier_elf).map_err(|e| anyhow!("load verifier: {e:?}"))?;
        for a in &accounts2 {
            let mut account = a.account.clone();
            if a.key == checkpoint.key {
                if let Some(data) = &seventh {
                    account.data = data.clone();
                }
            }
            svm.set_account(a.key, account).map_err(|e| anyhow!("set account: {e:?}"))?;
        }
        let instructions = [ComputeBudgetInstruction::set_compute_unit_limit(1_400_000), ComputeBudgetInstruction::request_heap_frame(256 * 1024), instruction.clone()];
        let message = Message::new_with_blockhash(&instructions, Some(&payer), &svm.latest_blockhash());
        let tx = Transaction::new_unsigned(message);
        let (error, meta) = match svm.send_transaction(tx) {
            Ok(m) => (None, m),
            Err(e) => (Some(format!("{:?}", e.err)), e.meta),
        };
        Ok(Outcome { error, logs: meta.logs, transaction_cu: meta.compute_units_consumed })
    };
    let record = |name: &str, o: &Outcome| json!({"mode": name, "error": o.error, "transaction_cu": o.transaction_cu, "pool_cu": consumed(&o.logs, &pool_id), "verifier_cu": consumed(&o.logs, &verifier_id), "logs": o.logs});

    // Control: the deployed verifier on the recorded accounts.
    let control = run(&deployed_elf, None)?;
    let recorded_pool = consumed(&stage2["meta"]["logMessages"].as_array().unwrap().iter().map(|l| l.as_str().unwrap().to_string()).collect::<Vec<_>>(), &pool_id);
    let control_ok = control.error.is_none() && consumed(&control.logs, &pool_id) == recorded_pool;
    // One transaction: certificate at the start of the seventh account, rest zero.
    let mut seventh = vec![0u8; checkpoint.account.data.len()];
    seventh[..certificate.len()].copy_from_slice(&certificate);
    let one = run(&one_tx_elf, Some(seventh.clone()))?;
    // Negatives: one changed certificate byte; the deployed checkpoint bytes in place of a certificate.
    let mut bad = seventh.clone();
    bad[77] ^= 1;
    let changed = run(&one_tx_elf, Some(bad))?;
    let stale = run(&one_tx_elf, None)?;
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
        "checkpoint_bytes_as_certificate_rejected": stale.error.is_some(),
    });
    println!("{summary}");
    let value = json!({
        "label": "FUTURE-VERSION EXPERIMENT — UNPROVED. Replay of a recorded devnet settlement in LiteSVM, signature verification off, real 1,400,000 CU limit",
        "source_revision": env::var("ASPIS_SOURCE_REVISION")?,
        "pool_elf_sha256": sha(&pool_elf), "deployed_verifier_elf_sha256": sha(&deployed_elf), "one_tx_verifier_elf_sha256": sha(&one_tx_elf),
        "recorded_signature": stage2["signature"], "recorded_slot": slot, "certificate_sha256": sha(&certificate),
        "runtime": {"litesvm": "0.16.0", "agave": "4.2.1", "heap_bytes": 262144},
        "summary": summary,
        "runs": [record("control-deployed-verifier", &control), record("one-transaction", &one), record("one-transaction-changed-certificate", &changed), record("one-transaction-checkpoint-bytes", &stale)],
    });
    fs::write(out, serde_json::to_string_pretty(&value)? + "\n")?;
    ensure!(control_ok, "control did not reproduce the recorded compute units");
    Ok(())
}
