//! PIN2 per-payment accounts: seed-derived upload and checkpoint accounts with
//! a fixed close sequence. Public data only; no key is opened here.
//!
//! Seed scheme (all seeds are 32 ASCII bytes, base = payer):
//!   proof attempt k (0..8): "p{k}" + tag      owner = upload program
//!   statement:              "s0"   + tag      owner = upload program
//!   checkpoint:             "c0"   + tag      owner = verifier
//!   negative checkpoint:    "n0"   + tag      owner = verifier (test runs only)
//! `tag` is 30 lowercase hex characters (15 bytes from the OS RNG), drawn once
//! per payment by the driver and retained before proving. The eight proof
//! attempt addresses are the prover's public mask nonces (Client64_accounts),
//! so they must be distinct and absent on chain before proving.
//!
//! Close order is fixed for every payment: proof, statement, checkpoint, in
//! one transaction, independent of any secret or of which attempt succeeded
//! (the selected attempt's address is public in TX1/TX2 already).
use anyhow::{anyhow, ensure, Result};
use serde_json::{json, Value};
use solana_program::pubkey::Pubkey;
use std::str::FromStr;

pub const UPLOAD_WRITE_TAG: u8 = aspis_upload::WRITE_TAG;
pub const UPLOAD_CLOSE_TAG: u8 = aspis_upload::CLOSE_TAG;
/// Verifier checkpoint close, fix/pin2-verifier-20261110 271869c946d (pool_route::CLOSE_CHECKPOINT_TAG).
pub const VERIFIER_CLOSE_TAG: u8 = 7;
/// Frozen upload chunk: 16 proof writes for 58,295 bytes, one statement write.
pub const CHUNK: usize = 3763;
pub const CHECKPOINT_BYTES: u64 = 1768;
pub const ATTEMPTS: usize = 8;
const SYSTEM: Pubkey = Pubkey::new_from_array([0; 32]);

fn pk(q: &Value, k: &str) -> Result<Pubkey> {
    let s = q[k].as_str().ok_or_else(|| anyhow!("missing {k}"))?;
    let p = Pubkey::from_str(s)?;
    ensure!(p.to_string() == s, "noncanonical {k}");
    Ok(p)
}

pub fn tag(q: &Value) -> Result<String> {
    let t = q["pin2_tag"].as_str().ok_or_else(|| anyhow!("missing pin2_tag"))?;
    ensure!(t.len() == 30 && t.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')), "pin2_tag must be 30 lowercase hex characters");
    Ok(t.to_string())
}

pub fn seed(role: char, index: usize, tag: &str) -> String {
    format!("{role}{index}{tag}")
}

pub fn derive(base: &Pubkey, seed: &str, owner: &Pubkey) -> Result<Pubkey> {
    ensure!((1..=32).contains(&seed.len()), "seed length");
    Pubkey::create_with_seed(base, seed, owner).map_err(|e| anyhow!("{e:?}"))
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|b| format!("{b:02x}")).collect()
}
fn meta(p: &Pubkey, s: bool, w: bool) -> Value {
    json!([p.to_string(), s, w])
}
fn ix(program: &Pubkey, accounts: Vec<Value>, data: &[u8]) -> Value {
    json!({"program": program.to_string(), "accounts": accounts, "data": hex(data)})
}
fn seeded(tag: u8, seed: &str, tail: &[u8]) -> Vec<u8> {
    let mut d = vec![tag, seed.len() as u8];
    d.extend_from_slice(seed.as_bytes());
    d.extend_from_slice(tail);
    d
}

/// System CreateAccountWithSeed with base = funder.
pub fn create_ix(payer: &Pubkey, seed: &str, lamports: u64, space: u64, owner: &Pubkey) -> Result<Value> {
    let to = derive(payer, seed, owner)?;
    let mut d = 3u32.to_le_bytes().to_vec();
    d.extend_from_slice(payer.as_ref());
    d.extend_from_slice(&(seed.len() as u64).to_le_bytes());
    d.extend_from_slice(seed.as_bytes());
    d.extend_from_slice(&lamports.to_le_bytes());
    d.extend_from_slice(&space.to_le_bytes());
    d.extend_from_slice(owner.as_ref());
    Ok(ix(&SYSTEM, vec![meta(payer, true, true), meta(&to, false, true)], &d))
}

pub fn write_ix(upload: &Pubkey, base: &Pubkey, seed: &str, offset: u32, bytes: &[u8]) -> Result<Value> {
    ensure!(!bytes.is_empty(), "empty write");
    let target = derive(base, seed, upload)?;
    let mut tail = offset.to_le_bytes().to_vec();
    tail.extend_from_slice(bytes);
    Ok(ix(upload, vec![meta(&target, false, true), meta(base, true, false)], &seeded(UPLOAD_WRITE_TAG, seed, &tail)))
}

pub fn close_ix(program: &Pubkey, tag: u8, base: &Pubkey, seed: &str) -> Result<Value> {
    let target = derive(base, seed, program)?;
    Ok(ix(program, vec![meta(&target, false, true), meta(base, true, true)], &seeded(tag, seed, &[])))
}

fn entry(base: &Pubkey, seed: String, owner: &Pubkey) -> Result<Value> {
    Ok(json!({"seed": seed, "address": derive(base, &seed, owner)?.to_string(), "owner": owner.to_string()}))
}

/// Every address and seed of one payment, from (payer, upload, verifier, tag).
pub fn layout(q: &Value) -> Result<Value> {
    let (base, upload, verifier, t) = (pk(q, "payer")?, pk(q, "upload_program")?, pk(q, "verifier")?, tag(q)?);
    let attempts: Vec<Value> = (0..ATTEMPTS).map(|k| entry(&base, seed('p', k, &t), &upload)).collect::<Result<_>>()?;
    let keys: Vec<Value> = attempts.iter().map(|a| a["address"].clone()).collect();
    for i in 0..ATTEMPTS {
        ensure!(!keys[..i].contains(&keys[i]), "duplicate attempt address");
    }
    Ok(json!({"route": "pin2-seeded-upload-v1", "base": base.to_string(), "upload_program": upload.to_string(),
              "verifier": verifier.to_string(), "pin2_tag": t, "proof_attempts": attempts, "proof_accounts": keys,
              "statement": entry(&base, seed('s', 0, &t), &upload)?, "checkpoint": entry(&base, seed('c', 0, &t), &verifier)?,
              "negative_checkpoint": entry(&base, seed('n', 0, &t), &verifier)?}))
}

/// Writes for one body in CHUNK ranges, in ascending offset order.
pub fn writes(q: &Value) -> Result<Value> {
    let (base, upload) = (pk(q, "payer")?, pk(q, "upload_program")?);
    let seed = q["seed"].as_str().ok_or_else(|| anyhow!("missing seed"))?;
    let body = super::super::unhex(q["body"].as_str().ok_or_else(|| anyhow!("missing body"))?);
    // Optional start offset (used only for the one-byte negative-test mutation and restore).
    let start = q.get("offset").map_or(Some(0), Value::as_u64).ok_or_else(|| anyhow!("offset"))? as usize;
    ensure!(!body.is_empty() && start.checked_add(body.len()).is_some_and(|e| e <= u32::MAX as usize), "body length");
    let list: Vec<Value> = body.chunks(CHUNK).enumerate()
        .map(|(i, c)| write_ix(&upload, &base, seed, (start + i * CHUNK) as u32, c)).collect::<Result<_>>()?;
    Ok(json!({"address": derive(&base, seed, &upload)?.to_string(), "count": list.len(), "chunk": CHUNK, "instructions": list}))
}

/// The fixed close transaction for a settled (or abandoned) payment:
/// [upload CLOSE proof attempt k, upload CLOSE statement, verifier CLOSE checkpoint].
pub fn close_plan(q: &Value) -> Result<Value> {
    let (base, upload, verifier, t) = (pk(q, "payer")?, pk(q, "upload_program")?, pk(q, "verifier")?, tag(q)?);
    let k = q["attempt_index"].as_u64().ok_or_else(|| anyhow!("missing attempt_index"))? as usize;
    ensure!(k < ATTEMPTS, "attempt_index");
    let order = [("proof", upload, UPLOAD_CLOSE_TAG, seed('p', k, &t)), ("statement", upload, UPLOAD_CLOSE_TAG, seed('s', 0, &t)),
                 ("checkpoint", verifier, VERIFIER_CLOSE_TAG, seed('c', 0, &t))];
    let mut ixs = Vec::new();
    let mut accounts = Vec::new();
    for (role, program, tag, s) in order {
        ixs.push(close_ix(&program, tag, &base, &s)?);
        accounts.push(json!({"role": role, "seed": s, "address": derive(&base, &s, &program)?.to_string(), "owner": program.to_string()}));
    }
    Ok(json!({"order": ["proof", "statement", "checkpoint"], "accounts": accounts, "instructions": ixs}))
}

/// One close instruction for a recorded leftover (recovery).
pub fn close_one(q: &Value) -> Result<Value> {
    let (base, program) = (pk(q, "payer")?, pk(q, "owner")?);
    let s = q["seed"].as_str().ok_or_else(|| anyhow!("missing seed"))?;
    let tag = match q["kind"].as_str() {
        Some("upload") => UPLOAD_CLOSE_TAG,
        Some("checkpoint") => VERIFIER_CLOSE_TAG,
        _ => return Err(anyhow!("kind must be upload or checkpoint")),
    };
    close_ix(&program, tag, &base, s)
}

pub fn dispatch(q: &Value) -> Result<Option<Value>> {
    Ok(Some(match q["action"].as_str() {
        Some("pin2_layout") => layout(q)?,
        Some("pin2_writes") => writes(q)?,
        Some("pin2_close") => close_plan(q)?,
        Some("pin2_close_one") => close_one(q)?,
        Some("pin2_create") => {
            let (payer, owner) = (pk(q, "payer")?, pk(q, "owner")?);
            let s = q["seed"].as_str().ok_or_else(|| anyhow!("missing seed"))?;
            let (lamports, space) = (q["lamports"].as_u64().ok_or_else(|| anyhow!("lamports"))?, q["space"].as_u64().ok_or_else(|| anyhow!("space"))?);
            json!({"address": derive(&payer, s, &owner)?.to_string(), "instruction": create_ix(&payer, s, lamports, space, &owner)?})
        }
        _ => return Ok(None),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    const TAG: &str = "00112233445566778899aabbccddee";
    fn q() -> Value {
        json!({"payer": Pubkey::new_from_array([0x11; 32]).to_string(), "upload_program": Pubkey::new_from_array([0x22; 32]).to_string(),
               "verifier": Pubkey::new_from_array([0x33; 32]).to_string(), "pin2_tag": TAG})
    }
    fn unhex(s: &str) -> Vec<u8> { super::super::super::unhex(s) }

    #[test]
    fn golden_derivations_match_python_client() {
        // Same vectors as scripts/PIN2_test_seed_accounts.py (hashlib sha256(base||seed||owner)).
        let l = layout(&q()).unwrap();
        assert_eq!(l["proof_accounts"][0], "6nPTTqm7ja3XgjsPt6kXXwtiEVH5nx2EVjdPuUExBreU");
        assert_eq!(l["proof_accounts"][7], "5Skhkx5FKaMHqfNw6HrJANBma1MnnkDWC7VKKupX9Bni");
        assert_eq!(l["statement"]["address"], "6JJqjatYYLJpjWwaTfjwVJgvyufrs56JLPVhkywQUiW8");
        assert_eq!(l["checkpoint"]["address"], "6z6Dya2a6xXCAmNfVVwHdkf8QKhYxUEcdhhBN9axnBTY");
        let keys = l["proof_accounts"].as_array().unwrap();
        assert_eq!(keys.len(), 8);
        // The planner accepts them as the eight mask-nonce accounts.
        assert!(super::super::client64_accounts::Accounts::parse(&json!({"proof_accounts": keys})).is_ok());
        for a in l["proof_attempts"].as_array().unwrap() {
            assert_eq!(a["seed"].as_str().unwrap().len(), 32);
        }
    }

    #[test]
    fn instruction_bytes_decode_in_the_upload_program() {
        let mut w = q();
        w["seed"] = json!(seed('p', 3, TAG));
        w["body"] = json!(hex(&vec![7u8; 58_295]));
        let plan = writes(&w).unwrap();
        assert_eq!(plan["count"], 16);
        for (i, ix) in plan["instructions"].as_array().unwrap().iter().enumerate() {
            let d = unhex(ix["data"].as_str().unwrap());
            match aspis_upload::decode(&d).unwrap() {
                aspis_upload::UploadInstruction::Write { seed: s, offset, bytes } => {
                    assert_eq!(s, seed('p', 3, TAG));
                    assert_eq!(offset as usize, i * CHUNK);
                    assert_eq!(bytes.len(), if i < 15 { CHUNK } else { 58_295 - 15 * CHUNK });
                }
                _ => panic!(),
            }
            assert_eq!(ix["accounts"][0][0], plan["address"]);
            assert_eq!(ix["accounts"][1], json!([q()["payer"], true, false]));
        }
        let mut m = w.clone();
        m["body"] = json!("ab");
        m["offset"] = json!(688);
        let one = writes(&m).unwrap();
        let d = unhex(one["instructions"][0]["data"].as_str().unwrap());
        assert_eq!(aspis_upload::decode(&d).unwrap(), aspis_upload::UploadInstruction::Write { seed: &seed('p', 3, TAG), offset: 688, bytes: &[0xab] });
        let mut c = q();
        c["attempt_index"] = json!(3);
        let close = close_plan(&c).unwrap();
        let ixs = close["instructions"].as_array().unwrap();
        assert_eq!(ixs.len(), 3);
        for (n, ix) in ixs.iter().enumerate() {
            let d = unhex(ix["data"].as_str().unwrap());
            assert_eq!(ix["accounts"][1], json!([q()["payer"], true, true]));
            assert_eq!(ix["accounts"][0][0], close["accounts"][n]["address"]);
            if n < 2 {
                assert!(matches!(aspis_upload::decode(&d).unwrap(), aspis_upload::UploadInstruction::Close { .. }));
                assert_eq!(ix["program"], q()["upload_program"]);
            } else {
                // W1's pool_route::is_close_checkpoint: [7, len, seed], len == seed bytes, 1..=32.
                assert_eq!((d[0], d[1] as usize, d.len()), (7, d.len() - 2, 34));
                assert_eq!(ix["program"], q()["verifier"]);
                assert_eq!(close["accounts"][2]["address"], "6z6Dya2a6xXCAmNfVVwHdkf8QKhYxUEcdhhBN9axnBTY");
            }
        }
        assert_eq!(close["accounts"][0]["address"], layout(&q()).unwrap()["proof_accounts"][3]);
        c["attempt_index"] = json!(8);
        assert!(close_plan(&c).is_err());
    }

    #[test]
    fn create_with_seed_bytes() {
        let payer = Pubkey::new_from_array([0x11; 32]);
        let v = create_ix(&payer, &seed('c', 0, TAG), 1234, 1768, &Pubkey::new_from_array([0x33; 32])).unwrap();
        let d = unhex(v["data"].as_str().unwrap());
        assert_eq!(&d[..4], &[3, 0, 0, 0]);
        assert_eq!(&d[4..36], payer.as_ref());
        assert_eq!(u64::from_le_bytes(d[36..44].try_into().unwrap()), 32);
        assert_eq!(&d[44..76], seed('c', 0, TAG).as_bytes());
        assert_eq!(u64::from_le_bytes(d[76..84].try_into().unwrap()), 1234);
        assert_eq!(u64::from_le_bytes(d[84..92].try_into().unwrap()), 1768);
        assert_eq!(&d[92..], &[0x33; 32]);
        assert_eq!(v["accounts"][1][0], "6z6Dya2a6xXCAmNfVVwHdkf8QKhYxUEcdhhBN9axnBTY");
    }

    #[test]
    fn bad_tags_rejected() {
        for t in ["", "00112233445566778899AABBCCDDEE", "00112233445566778899aabbccdde", "00112233445566778899aabbccddeeff", "0011223344556677889-aabbccddee"] {
            let mut v = q();
            v["pin2_tag"] = json!(t);
            assert!(layout(&v).is_err(), "{t}");
        }
    }
}
