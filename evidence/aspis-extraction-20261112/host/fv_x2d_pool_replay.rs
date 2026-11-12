//! X2d (tool record, not a proof): replay RECORDED devnet Pool transactions that carry one Pool instruction
//! (pool-initialize, deposit-0, deposit-1, forest-checkpoint of the PIN2 run) in LiteSVM from their recorded
//! pre-state, once per given Pool ELF, and report the Pool's compute units from the program log.
//!
//! The setup follows one_tx_replay: signature verification off, the recorded Clock slot, devnet's rent
//! (every recorded account holds (128 + space) * 5,080 lamports), the recorded accounts (non-executable,
//! existing) set as recorded, the Pool ELF at the recorded Pool address, the recorded instruction as recorded,
//! preceded by a compute-unit-limit instruction of 1,400,000 (the recorded runs report "of 1400000").
//!
//! Checks per run: the first ELF given is the control (the deployed devnet Pool): its Pool compute must equal
//! the recorded figure and its final state the recorded post-state (payer lamports excepted, the fee differs);
//! every other ELF's final state is compared with the control's (every account, the payer included).
//!
//! usage: x2d_pool_replay <transactions.json> <label=pool.so>[,<label=pool.so>...] <tx-name>[,<tx-name>...] <out.json>
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
fn base58(a: &Address) -> String {
    LegacyPubkey::new_from_array(a.to_bytes()).to_string()
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
/// (key, Some((lamports, owner, data))) per account of a snapshot; None for an absent account.
type State = Vec<(String, Option<(u64, String, Vec<u8>)>)>;
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
fn differing(a: &State, b: &State, skip_lamports: &[&str]) -> Vec<String> {
    let mut out = vec![];
    for (key, left) in a {
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
    ensure!(args.len() == 5, "usage: x2d_pool_replay <transactions.json> <label=pool.so>[,...] <tx-name>[,...] <out.json>");
    let all: Value = serde_json::from_slice(&fs::read(&args[1])?)?;
    let elfs: Vec<(String, String, Vec<u8>)> = args[2]
        .split(',')
        .map(|s| {
            let (label, path) = s.split_once('=').context("label=path")?;
            Ok((label.to_string(), path.to_string(), fs::read(path).with_context(|| path.to_string())?))
        })
        .collect::<Result<_>>()?;
    let names: Vec<&str> = args[3].split(',').collect();
    let out = Path::new(&args[4]);
    ensure!(!out.exists(), "unchanged measurement rerun forbidden: {}", out.display());
    let pool_id = all["programs"]["pool"].as_str().context("pool id")?.to_string();
    let mut results = vec![];
    let mut ok_all = true;
    for name in &names {
        let tx = all["transactions"].as_array().unwrap().iter().find(|t| t["name"] == *name).cloned().ok_or_else(|| anyhow!("no transaction {name}"))?;
        ensure!(tx["instructions"].as_array().map(|a| a.len()) == Some(1), "{name}: one recorded instruction expected");
        let ix = &tx["instructions"][0];
        ensure!(ix["program"] == pool_id.as_str(), "{name}: not a Pool instruction");
        let payer = address(tx["keys"][0].as_str().context("payer")?)?;
        let payer_key = tx["keys"][0].as_str().unwrap().to_string();
        let instruction = Instruction {
            program_id: address(&pool_id)?,
            accounts: ix["accounts"].as_array().context("accounts")?.iter().map(|m| {
                let key = address(m["key"].as_str().unwrap())?;
                let signer = m["is_signer"].as_bool().unwrap();
                Ok(if m["is_writable"].as_bool().unwrap() { AccountMeta::new(key, signer) } else { AccountMeta::new_readonly(key, signer) })
            }).collect::<Result<Vec<_>>>()?,
            data: unhex(ix["data_hex"].as_str().context("data_hex")?)?,
        };
        let slot = tx["clock"]["slot"].as_u64().context("slot")?;
        let pre = recorded_state(&tx["pre"])?;
        let recorded_post = recorded_state(&tx["post"])?;
        let recorded_logs: Vec<String> = tx["meta"]["logMessages"].as_array().unwrap().iter().map(|l| l.as_str().unwrap().to_string()).collect();
        let recorded_pool_cu = consumed(&recorded_logs, &pool_id);
        let mut control_post: Option<State> = None;
        for (k, (label, path, elf)) in elfs.iter().enumerate() {
            let mut svm = LiteSVM::new().with_sigverify(false);
            svm.warp_to_slot(slot);
            let mut rent = Vec::with_capacity(17);
            rent.extend_from_slice(&2_540u64.to_le_bytes());
            rent.extend_from_slice(&2.0f64.to_le_bytes());
            rent.push(50);
            svm.set_account(address("SysvarRent111111111111111111111111111111111")?, Account { lamports: 1_009_200, data: rent, owner: address("Sysvar1111111111111111111111111111111111111")?, executable: false, rent_epoch: u64::MAX }).map_err(|e| anyhow!("rent sysvar: {e:?}"))?;
            svm.add_program(address(&pool_id)?, elf).map_err(|e| anyhow!("load pool: {e:?}"))?;
            for (key, account) in &pre {
                if let Some((lamports, owner, data)) = account {
                    svm.set_account(address(key)?, Account { lamports: *lamports, data: data.clone(), owner: address(owner)?, executable: false, rent_epoch: u64::MAX }).map_err(|e| anyhow!("set account: {e:?}"))?;
                }
            }
            let instructions = [ComputeBudgetInstruction::set_compute_unit_limit(1_400_000), instruction.clone()];
            let message = Message::new_with_blockhash(&instructions, Some(&payer), &svm.latest_blockhash());
            let (error, meta) = match svm.send_transaction(Transaction::new_unsigned(message)) {
                Ok(m) => (None, m),
                Err(e) => (Some(format!("{:?}", e.err)), e.meta),
            };
            let mut post: State = vec![];
            for (key, _) in &pre {
                let account = svm.get_account(&address(key)?);
                post.push((key.clone(), account.filter(|a| a.lamports > 0 || !a.data.is_empty()).map(|a| (a.lamports, base58(&a.owner), a.data))));
            }
            let pool_cu = consumed(&meta.logs, &pool_id);
            let (check, ok) = if k == 0 {
                let d = differing(&post, &recorded_post, &[payer_key.as_str()]);
                let ok = error.is_none() && pool_cu == recorded_pool_cu && d.is_empty();
                control_post = Some(post.clone());
                (json!({"control": true, "pool_cu_equals_recorded": pool_cu == recorded_pool_cu, "final_state_equals_recorded_except_payer_fee": d.is_empty(), "differing": d}), ok)
            } else {
                let d = differing(&post, control_post.as_ref().unwrap(), &[]);
                let ok = error.is_none() && d.is_empty();
                (json!({"control": false, "final_state_equals_control": d.is_empty(), "differing": d}), ok)
            };
            ok_all &= ok;
            println!("{name} {label} error={:?} pool_cu={:?} transaction_cu={} recorded_pool_cu={:?} ok={ok}", error, pool_cu, meta.compute_units_consumed, recorded_pool_cu);
            results.push(json!({"transaction": name, "label": label, "pool_elf": path, "pool_elf_sha256": sha(elf), "error": error, "pool_cu": pool_cu, "transaction_cu": meta.compute_units_consumed, "recorded_pool_cu": recorded_pool_cu, "recorded_signature": tx["signature"], "recorded_slot": slot, "check": check, "logs": meta.logs}));
        }
    }
    let value = json!({
        "label": "X2d tool record, not a proof: replay of recorded devnet Pool transactions in LiteSVM, signature verification off",
        "source_revision": env::var("ASPIS_SOURCE_REVISION").unwrap_or_default(),
        "runtime": {"litesvm": "0.16.0"},
        "all_ok": ok_all,
        "runs": results,
    });
    fs::write(out, serde_json::to_string_pretty(&value)? + "\n")?;
    ensure!(ok_all, "a control or a comparison failed; see {}", out.display());
    Ok(())
}
