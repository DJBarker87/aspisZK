//! Aspis one-transaction verifier: can a withdrawal be redirected?
//!
//! Replays the RECORDED devnet withdrawal settlement (PIN2 run of 11 November
//! 2026) in LiteSVM from its recorded pre-state, with the deployed Pool program
//! and the one-transaction verifier, the recorded proof re-packed into the
//! one-transaction format. Then it tries to move the payout:
//!
//! - honest: nothing changed. Must settle and pay the recorded destination.
//! - redirect-request-and-account: the destination is replaced, by another
//!   token account of the same mint, both in the request the proof is checked
//!   against and in the account list. The attack R1 allowed before PIN2.
//! - redirect-account-only: only the account that would receive the tokens.
//! - redirect-request-only: only the destination named in the request.
//! - other-payer-honest: a third party submits the unchanged settlement and
//!   pays for it. Expected to SETTLE, to the recorded destination: the proof
//!   authorises the payment, not the submitter.
//! - other-payer-redirect: that third party also redirects. Must fail.
//!
//! Every redirect must fail and leave every account as it was (apart from the
//! fee of the failed transaction); in particular the other token account and
//! the vault keep their balances.
//!
//! Signature verification is off (recorded keys are not available). The
//! second token account is a copy of the recorded destination's account under
//! a new address, so it has the same mint and owner.
//!
//! usage: one_tx_redirect <transactions.json> <pool.so> <verifier-one-tx.so> <out.json>
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
        out.push(Recorded {
            key: address(a["key"].as_str().context("key")?)?,
            account: Account { lamports: a["lamports"].as_u64().context("lamports")?, data, owner: address(a["owner"].as_str().context("owner")?)?, executable: false, rent_epoch: u64::MAX },
        });
    }
    Ok(out)
}
/// SPL token account balance (bytes 64..72), or `None` if the account is absent.
fn tokens(svm: &LiteSVM, key: &Address) -> Option<u64> {
    svm.get_account(key).filter(|a| a.data.len() == 165).map(|a| u64::from_le_bytes(a.data[64..72].try_into().unwrap()))
}
/// Positions of `needle` in `haystack`.
fn occurrences(haystack: &[u8], needle: &[u8]) -> Vec<usize> {
    (0..=haystack.len().saturating_sub(needle.len())).filter(|&i| &haystack[i..i + needle.len()] == needle).collect()
}

fn main() -> Result<()> {
    ensure!(!cfg!(debug_assertions), "release build only");
    let args: Vec<_> = env::args().collect();
    ensure!(args.len() == 5, "usage: one_tx_redirect <transactions.json> <pool.so> <verifier-one-tx.so> <out.json>");
    let all: Value = serde_json::from_slice(&fs::read(&args[1])?)?;
    let pool_elf = fs::read(&args[2])?;
    let one_tx_elf = fs::read(&args[3])?;
    let out = Path::new(&args[4]);
    ensure!(!out.exists(), "unchanged measurement rerun forbidden: {}", out.display());
    let pool_id = all["programs"]["pool"].as_str().context("pool id")?.to_string();
    let verifier_id = all["programs"]["verifier"].as_str().context("verifier id")?.to_string();
    let upload = address(all["upload_program"].as_str().context("upload id")?)?;
    let find = |name: &str| all["transactions"].as_array().unwrap().iter().find(|t| t["name"] == name).cloned().ok_or_else(|| anyhow!("no transaction {name}"));
    let stage1 = find("withdrawal-stage1")?;
    let stage2 = find("withdrawal-stage2")?;
    let recorded_ix = &stage2["instructions"][0];
    ensure!(recorded_ix["program"] == pool_id.as_str(), "recorded settlement is not a Pool instruction");
    let payer = address(stage2["keys"][0].as_str().context("payer")?)?;
    let metas = recorded_ix["accounts"].as_array().context("accounts")?.iter().map(|m| {
        let key = address(m["key"].as_str().unwrap())?;
        let signer = m["is_signer"].as_bool().unwrap();
        Ok(if m["is_writable"].as_bool().unwrap() { AccountMeta::new(key, signer) } else { AccountMeta::new_readonly(key, signer) })
    }).collect::<Result<Vec<_>>>()?;
    let data = unhex(recorded_ix["data_hex"].as_str().context("data_hex")?)?;
    let slot = stage2["clock"]["slot"].as_u64().context("slot")?;
    let accounts2 = recorded_accounts(&stage2)?;
    let accounts1 = recorded_accounts(&stage1)?;
    let proof = accounts2.iter().find(|a| a.account.owner == upload && a.account.data.len() > 50_000).context("proof buffer")?;
    let public = accounts1.iter().find(|a| a.account.owner == upload && a.account.data.len() == 1880).context("public statement")?;
    let prefix = aspis_statement::pool_v1::POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let statement = aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(&public.account.data).map_err(|e| anyhow!("statement: {e:?}"))?;
    let (destination_bytes, amount) = match &statement {
        aspis_statement::pool_v1::PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => (public.destination_token_account, u64::from(public.amount)),
        _ => return Err(anyhow!("recorded statement is not a withdrawal")),
    };
    let destination = Address::new_from_array(destination_bytes);
    let packed = aspis_r1_cost_probe::verifier::candidate::one_tx::pack(statement.semantic_public(), &proof.account.data[prefix..], Sha).map_err(|e| anyhow!("re-pack: {e:?}"))?;
    let mut buffer = proof.account.data[..prefix].to_vec();
    buffer.extend_from_slice(&packed);

    // Where the destination sits in the transaction: once among the accounts, once in the request bytes.
    let in_accounts: Vec<usize> = metas.iter().enumerate().filter(|(_, m)| m.pubkey == destination).map(|(i, _)| i).collect();
    let in_request = occurrences(&data, &destination_bytes);
    ensure!(in_accounts.len() == 1 && in_request.len() == 1, "destination must occur once in the accounts ({in_accounts:?}) and once in the request ({in_request:?})");
    let recorded_destination = accounts2.iter().find(|a| a.key == destination).context("recorded destination account")?;
    let vault = accounts2.iter().filter(|a| a.account.data.len() == 165 && a.key != destination).map(|a| a.key).next().context("vault token account")?;

    // The second token account: same bytes as the destination (same mint, same owner), other address.
    let other = Address::new_from_array(aspis_core::Digest32::digest(&Sha, &[&b"aspis one_tx_redirect other token account"[..]]));
    let other_payer = Address::new_from_array(aspis_core::Digest32::digest(&Sha, &[&b"aspis one_tx_redirect other payer"[..]]));
    ensure!(other != destination && !metas.iter().any(|m| m.pubkey == other || m.pubkey == other_payer), "derived test addresses collide");
    let system = address("11111111111111111111111111111111")?;

    let attempt = |name: &str, change_request: bool, change_account: bool, change_payer: bool| -> Result<Value> {
        let mut svm = LiteSVM::new().with_sigverify(false);
        svm.warp_to_slot(slot);
        let mut rent = Vec::with_capacity(17);
        rent.extend_from_slice(&2_540u64.to_le_bytes());
        rent.extend_from_slice(&2.0f64.to_le_bytes());
        rent.push(50);
        svm.set_account(address("SysvarRent111111111111111111111111111111111")?, Account { lamports: 1_009_200, data: rent, owner: address("Sysvar1111111111111111111111111111111111111")?, executable: false, rent_epoch: u64::MAX }).map_err(|e| anyhow!("rent sysvar: {e:?}"))?;
        svm.add_program(address(&pool_id)?, &pool_elf).map_err(|e| anyhow!("load pool: {e:?}"))?;
        svm.add_program(address(&verifier_id)?, &one_tx_elf).map_err(|e| anyhow!("load verifier: {e:?}"))?;
        for a in &accounts2 {
            let mut account = a.account.clone();
            if a.key == proof.key {
                account.data = buffer.clone();
            }
            svm.set_account(a.key, account).map_err(|e| anyhow!("set account: {e:?}"))?;
        }
        svm.set_account(other, recorded_destination.account.clone()).map_err(|e| anyhow!("other token account: {e:?}"))?;
        svm.set_account(other_payer, Account { lamports: 1_000_000_000, data: vec![], owner: system, executable: false, rent_epoch: u64::MAX }).map_err(|e| anyhow!("other payer: {e:?}"))?;

        let mut accounts = metas.clone();
        let mut request = data.clone();
        if change_account {
            accounts[in_accounts[0]].pubkey = other;
        }
        if change_request {
            request[in_request[0]..in_request[0] + 32].copy_from_slice(&other.to_bytes());
        }
        let fee_payer = if change_payer { other_payer } else { payer };
        if change_payer {
            for m in accounts.iter_mut().filter(|m| m.pubkey == payer) {
                m.pubkey = other_payer;
            }
        }
        // Everything the transaction can touch, before.
        let mut watched: Vec<Address> = accounts2.iter().map(|a| a.key).collect();
        watched.extend([other, other_payer]);
        for m in &accounts {
            if !watched.contains(&m.pubkey) {
                watched.push(m.pubkey);
            }
        }
        let snapshot = |svm: &LiteSVM| -> Vec<(Address, Option<(u64, Address, Vec<u8>)>)> {
            watched.iter().map(|k| (*k, svm.get_account(k).filter(|a| !a.executable && (a.lamports > 0 || !a.data.is_empty())).map(|a| (a.lamports, a.owner, a.data)))).collect()
        };
        let before = snapshot(&svm);
        let balances = |svm: &LiteSVM| json!({"recorded_destination": tokens(svm, &destination), "other_token_account": tokens(svm, &other), "vault": tokens(svm, &vault)});
        let tokens_before = balances(&svm);
        let instruction = Instruction { program_id: address(&pool_id)?, accounts, data: request };
        let instructions = [ComputeBudgetInstruction::set_compute_unit_limit(1_400_000), ComputeBudgetInstruction::request_heap_frame(256 * 1024), instruction];
        let message = Message::new_with_blockhash(&instructions, Some(&fee_payer), &svm.latest_blockhash());
        let (error, meta) = match svm.send_transaction(Transaction::new_unsigned(message)) {
            Ok(m) => (None, m),
            Err(e) => (Some(format!("{:?}", e.err)), e.meta),
        };
        let after = snapshot(&svm);
        // Accounts that changed, ignoring the fee taken from whoever paid for the transaction.
        let changed: Vec<String> = before.iter().zip(&after).filter(|(b, a)| {
            if b.0 == fee_payer {
                match (&b.1, &a.1) {
                    (Some(x), Some(y)) => x.1 != y.1 || x.2 != y.2,
                    _ => true,
                }
            } else {
                b.1 != a.1
            }
        }).map(|(b, _)| base58(&b.0)).collect();
        Ok(json!({"attempt": name, "request_destination_changed": change_request, "paid_account_changed": change_account, "other_payer": change_payer,
                  "error": error, "transaction_cu": meta.compute_units_consumed, "tokens_before": tokens_before, "tokens_after": balances(&svm),
                  "accounts_changed_apart_from_the_fee": changed, "logs": meta.logs}))
    };

    let honest = attempt("honest", false, false, false)?;
    let both = attempt("redirect-request-and-account", true, true, false)?;
    let account_only = attempt("redirect-account-only", false, true, false)?;
    let request_only = attempt("redirect-request-only", true, false, false)?;
    let relay = attempt("other-payer-honest", false, false, true)?;
    let relay_redirect = attempt("other-payer-redirect", true, true, true)?;

    let paid = |v: &Value, who: &str| v["tokens_after"][who].as_u64().unwrap_or(0) as i128 - v["tokens_before"][who].as_u64().unwrap_or(0) as i128;
    let settled_to_destination = |v: &Value| v["error"].is_null() && paid(v, "recorded_destination") == amount as i128 && paid(v, "other_token_account") == 0 && paid(v, "vault") == -(amount as i128);
    let rejected_cleanly = |v: &Value| !v["error"].is_null() && v["accounts_changed_apart_from_the_fee"].as_array().map(|a| a.is_empty()) == Some(true)
        && paid(v, "recorded_destination") == 0 && paid(v, "other_token_account") == 0 && paid(v, "vault") == 0;
    let summary = json!({
        "withdrawal_amount_base_units": amount,
        "honest_settles_to_the_recorded_destination": settled_to_destination(&honest),
        "redirect_request_and_account_rejected_cleanly": rejected_cleanly(&both),
        "redirect_account_only_rejected_cleanly": rejected_cleanly(&account_only),
        "redirect_request_only_rejected_cleanly": rejected_cleanly(&request_only),
        "other_payer_honest_settles_to_the_recorded_destination": settled_to_destination(&relay),
        "other_payer_redirect_rejected_cleanly": rejected_cleanly(&relay_redirect),
        "errors": {"redirect_request_and_account": both["error"], "redirect_account_only": account_only["error"], "redirect_request_only": request_only["error"], "other_payer_redirect": relay_redirect["error"]},
        "compute_units": {"honest": honest["transaction_cu"], "redirect_request_and_account": both["transaction_cu"], "redirect_account_only": account_only["transaction_cu"], "redirect_request_only": request_only["transaction_cu"]},
    });
    println!("{summary}");
    let value = json!({
        "label": "Aspis one-transaction verifier, UNPROVED. Destination-redirect attempts on a recorded devnet withdrawal, replayed in LiteSVM with signature verification off and the real 1,400,000 CU limit",
        "source_revision": env::var("ASPIS_SOURCE_REVISION")?,
        "pool_elf_sha256": sha(&pool_elf), "one_tx_verifier_elf_sha256": sha(&one_tx_elf),
        "recorded_signature": stage2["signature"], "recorded_slot": slot, "one_transaction_proof_sha256": sha(&packed),
        "recorded_destination": base58(&destination), "other_token_account": base58(&other), "other_payer": base58(&other_payer),
        "runtime": {"litesvm": "0.16.0", "agave": "4.2.1", "heap_bytes": 262144},
        "summary": summary,
        "attempts": [honest, both, account_only, request_only, relay, relay_redirect],
    });
    fs::write(out, serde_json::to_string_pretty(&value)? + "\n")?;
    let s = &value["summary"];
    for k in ["honest_settles_to_the_recorded_destination", "redirect_request_and_account_rejected_cleanly", "redirect_account_only_rejected_cleanly", "redirect_request_only_rejected_cleanly", "other_payer_redirect_rejected_cleanly"] {
        ensure!(s[k] == true, "FAILED: {k}");
    }
    Ok(())
}
