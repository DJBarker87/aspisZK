//! R1 privacy read budget (r1p-readbudget, 2026-10-19): instrumented count of
//! the hash calls of one prover attempt, eight-way (shipped) and binary
//! (compact-binary candidate), on the deterministic R0 fixture. Each call is
//! classified by its first input slice (domain string, or the one/two-byte
//! node/leaf tag) and counted twice: calls, and distinct digests (= distinct
//! addresses, SHA-256 being collision-free in practice). Prints JSON.
use aspis_core::HashFn;
use aspis_prover::HOST_HASH;
use aspis_r1_cost_probe::{prover, transport::Variant};
use std::collections::{BTreeMap, HashSet};
use std::sync::Mutex;

struct Class {
    calls: u64,
    distinct: HashSet<[u8; 32]>,
}
static LOG: Mutex<BTreeMap<String, Class>> = Mutex::new(BTreeMap::new());

fn class_of(parts: &[&[u8]]) -> String {
    let first = parts.first().copied().unwrap_or(&[]);
    let printable = !first.is_empty() && first.iter().all(|&b| (0x20..0x7f).contains(&b));
    if printable {
        return String::from_utf8_lossy(first).into_owned();
    }
    if first.len() <= 2 {
        return format!("tag:{}", first.iter().map(|b| format!("{b:02x}")).collect::<String>());
    }
    // Transcript sponge steps: 32-byte state followed by a short opcode.
    match parts.get(1) {
        Some(op) if op.len() <= 2 => format!(
            "state{}+op:{}",
            first.len(),
            op.iter().map(|b| format!("{b:02x}")).next().unwrap_or_default()
        ),
        _ => format!("raw{}", first.len()),
    }
}

fn counting(parts: &[&[u8]]) -> [u8; 32] {
    let out = HOST_HASH(parts);
    let key = class_of(parts);
    let mut log = LOG.lock().unwrap();
    let c = log.entry(key).or_insert_with(|| Class { calls: 0, distinct: HashSet::new() });
    c.calls += 1;
    c.distinct.insert(out);
    out
}

fn take() -> serde_json::Value {
    let mut log = LOG.lock().unwrap();
    let mut classes = serde_json::Map::new();
    let (mut calls, mut distinct) = (0u64, 0u64);
    for (k, c) in log.iter() {
        calls += c.calls;
        distinct += c.distinct.len() as u64;
        classes.insert(k.clone(), serde_json::json!({"calls": c.calls, "distinct": c.distinct.len()}));
    }
    log.clear();
    serde_json::json!({"total_calls": calls, "total_distinct": distinct, "classes": classes})
}

fn main() {
    assert!(!cfg!(debug_assertions), "release build required");
    let raw: HashFn = HOST_HASH;
    let hash: HashFn = counting;
    let fixture = aspis_prover::r0_fixture::prepare(false);
    let public = aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(&fixture.statement).unwrap();
    let seed = raw(&[b"UNPROVED:R1:r1p-readbudget-count", &public]);
    take();
    let (eight, _) = prover::prove_masked_fixture(fixture.public(), &fixture.compiled, Variant::S2, hash, &seed).unwrap();
    let e = take();
    let (binary, _) = prover::prove_masked_fixture_candidate(fixture.public(), &fixture.compiled, hash, &seed).unwrap();
    let b = take();
    println!(
        "{}",
        serde_json::to_string_pretty(&serde_json::json!({
            "fixture": "aspis_prover::r0_fixture::prepare(false), Variant::S2",
            "eight_way": {"proof_bytes": eight.len(), "count": e},
            "binary": {"proof_bytes": binary.len(), "count": b},
        }))
        .unwrap()
    );
}
