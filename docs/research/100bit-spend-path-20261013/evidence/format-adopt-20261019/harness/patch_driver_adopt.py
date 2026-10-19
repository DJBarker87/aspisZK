#!/usr/bin/env python3
"""Derive the format-adoption measurement driver from the Pool B1 driver.

usage: patch_driver_adopt.py <sweep-crate-dir>
Input: tools/r1-cost-probe-sweep of the cu-bound2 host tree (pool_gate.rs
sha256 747cf4df..., the pool-b1 `measure` driver that produced the B1 CU
figures), built against this branch's tree. The adopted default prover and
verifier (PREREG-PROOF-SIZE-2) are used through their unchanged names
(`prover::prove_masked_{fixture,attempt}`); the edits are:
- the canonical-length check uses the adopted fixed length
  (`verifier::PROOF_BYTES`, 57,607) instead of the retired eight-way
  `View::proof_bytes`;
- right after proving, the default verifier runs natively (stage 1 split
  10, strict and authenticated stage 2) and the dense verifier; the 22
  queries are read from the checkpoint and per-slot node counts printed
  (FORMAT_ADOPT_NATIVE=...);
- R1_PROOF_SIZE_EXPECT_PUBLIC=<file>: the generated ASF8 statement must equal
  that file (same witness as the saved fixture);
- R1_PROOF_SIZE_UPLOAD_PROBE=1: print serialized TxV1/TxV0 sizes of the
  driver's lifecycle write (tag 5 || u32 offset || chunk) and of the wallet's
  upload instruction shape (tag 1 || u32 offset || u32 length || chunk; same
  accounts and signers), the exact maximum chunk of each, and stop.
"""
import hashlib, sys
from pathlib import Path

d = Path(sys.argv[1])
src = d / 'src/bin/pool_gate.rs'
s = src.read_text()
assert hashlib.sha256(s.encode()).hexdigest().startswith('747cf4df'), 'unexpected driver input'

def rep(a, b, n=1):
    global s
    assert s.count(a) == n, (a[:80], s.count(a))
    s = s.replace(a, b)

rep('use aspis_r1_cost_probe::{prover, transport::Variant, verifier::View};',
    '''use aspis_r1_cost_probe::{prover, transport::Variant, verifier};

/// Native adopted-format checks and per-slot node counts.
fn adopted_native(full_public_bytes: &[u8], proof: &[u8]) -> Result<serde_json::Value> {
    use aspis_r1_cost_probe::{compact, multiproof};
    let hash = aspis_core::digest::LegacyHashFn(HOST_HASH);
    let st = decode_pool_v1_pair_forest_terminal_statement_v1(full_public_bytes).map_err(|e| anyhow!("decode ASF8: {e:?}"))?;
    let t0 = std::time::Instant::now();
    let ck = verifier::tx1(st.semantic_public(), full_public_bytes, proof, verifier::SPLIT, hash, None).map_err(|e| anyhow!("native tx1: {e:?}"))?;
    verifier::tx2(full_public_bytes, proof, &ck, hash, None).map_err(|e| anyhow!("native tx2: {e:?}"))?;
    verifier::tx2_authenticated(full_public_bytes, proof, &ck, hash, None).map_err(|e| anyhow!("native tx2_authenticated: {e:?}"))?;
    let verify_seconds = t0.elapsed().as_secs_f64();
    aspis_r1_cost_probe::dense::verify(st.semantic_public(), proof, HOST_HASH).map_err(|e| anyhow!("dense: {e:?}"))?;
    let queries: Vec<u32> = (0..22).map(|i| u32::from_le_bytes(ck[320 + 4 * i..324 + 4 * i].try_into().unwrap())).collect();
    let mut nodes = Vec::new();
    for (lo, hi) in [(0usize, compact::SPLIT), (compact::SPLIT, 22)] {
        for t in 0..3 {
            let mut idx: Vec<u32> = queries[lo..hi].iter().map(|&u| if t == 2 { u / 4 } else { u }).collect();
            idx.sort();
            idx.dedup();
            nodes.push(multiproof::node_count(multiproof::Arity::Two, &idx).unwrap());
        }
    }
    let total: usize = nodes.iter().sum();
    Ok(serde_json::json!({"native_tx1_tx2_tx2_authenticated": "accepted", "dense": "accepted", "stored_bytes": proof.len(),
        "proof_sha256": format!("{:x}", Sha256::digest(proof)), "queries": queries, "slot_nodes": nodes, "total_nodes": total,
        "variable_length_bytes": compact::FIXED + 32 * total, "native_verify_seconds": verify_seconds}))
}''')
rep('''        proof_body.len() == View::proof_bytes(Variant::S2),
        "R1 S2 proof body has the wrong canonical length"
    );''', '''        proof_body.len() == verifier::PROOF_BYTES,
        "R1 S2 proof body has the wrong canonical length"
    );
    if let Ok(path) = std::env::var("R1_PROOF_SIZE_EXPECT_PUBLIC") {
        ensure!(fs::read(&path)? == full_public_bytes, "generated ASF8 differs from {path}");
        eprintln!("PROOF_SIZE_PUBLIC_MATCHES={path}");
    }
    let native = adopted_native(&full_public_bytes, &proof_body)?;
    eprintln!("FORMAT_ADOPT_NATIVE={native}");''')
rep('''    let mut svm = LiteSVM::new();''', '''    let mut svm = LiteSVM::new();
    if std::env::var("R1_PROOF_SIZE_UPLOAD_PROBE").as_deref() == Ok("1") {
        let authority = Keypair::new();
        let target = legacy(Keypair::new().pubkey().to_bytes());
        let driver_ix = |chunk: usize| lifecycle_instruction(verifier_program, target, legacy(authority.pubkey().to_bytes()), lifecycle_write_data(0, &vec![0xa5; chunk]));
        let wallet_ix = |chunk: usize| {
            let mut data = vec![1u8];
            data.extend_from_slice(&0u32.to_le_bytes());
            data.extend_from_slice(&(chunk as u32).to_le_bytes());
            data.extend_from_slice(&vec![0xa5; chunk]);
            lifecycle_instruction(verifier_program, target, legacy(authority.pubkey().to_bytes()), data)
        };
        for (shape, make) in [("driver-tag5", &driver_ix as &dyn Fn(usize) -> Instruction), ("wallet-tag1", &wallet_ix)] {
            for version in [TxVersion::V1, TxVersion::V0] {
                let limit = version.target_bytes();
                for chunk in [0usize, 100, 800, 900, 960, 3_763, 3_767] {
                    let tx = transaction_with_signers(&svm, &payer, make(chunk), &[&authority], version)?;
                    let bytes = wincode::serialize(&tx)?.len();
                    eprintln!("UPLOAD_TX shape={shape} version={} chunk={chunk} serialized={bytes} overhead={}", version.display_name(), bytes as i64 - chunk as i64);
                }
                let mut best = 0usize;
                let mut chunk = 1usize;
                loop {
                    let Ok(tx) = transaction_with_signers(&svm, &payer, make(chunk), &[&authority], version) else { break };
                    if wincode::serialize(&tx)?.len() > limit { break; }
                    best = chunk;
                    chunk += 1;
                }
                eprintln!("UPLOAD_MAX shape={shape} version={} limit={limit} max_chunk={best}", version.display_name());
            }
        }
        return Ok(());
    }''')
src.write_text(s)
print(hashlib.sha256(s.encode()).hexdigest())
