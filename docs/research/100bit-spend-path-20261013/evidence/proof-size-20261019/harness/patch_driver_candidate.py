#!/usr/bin/env python3
"""Derive the proof-size candidate driver from the Pool B1 measurement driver.

usage: patch_driver_candidate.py <sweep-crate-dir>
Input: tools/r1-cost-probe-sweep of the cu-bound2 host tree (pool_gate.rs
sha256 747cf4df..., the pool-b1 `measure` driver). Edits, all behind the new
cargo feature `compact-binary` (default build unchanged):
- proof generation calls the candidate prover (compact binary-multiproof);
- the canonical-length check uses the candidate's fixed length;
- right after proving, the candidate verifier runs natively (stage 1 split
  10, strict and authenticated stage 2), the 22 queries are read from the
  checkpoint and per-slot node counts printed (PROOF_SIZE_NATIVE=...);
- R1_PROOF_SIZE_EXPECT_PUBLIC=<file>: the generated ASF8 statement must equal
  that file (same witness as the saved fixture);
- R1_PROOF_SIZE_NATIVE_ONLY=1: stop after the native checks (S2);
- R1_PROOF_SIZE_UPLOAD_PROBE=1: print serialized sizes of lifecycle write
  transactions (TxV1 and TxV0) and stop (measurement 3).
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

cargo = (d / 'Cargo.toml').read_text()
cargo = cargo.replace('private-leaf-salts = ["aspis-r1-cost-probe/private-leaf-salts"]\n',
    'private-leaf-salts = ["aspis-r1-cost-probe/private-leaf-salts"]\n'
    'compact-binary = ["private-leaf-salts", "aspis-r1-cost-probe/compact-binary"]\n', 1)
(d / 'Cargo.toml').write_text(cargo)

rep('prover::prove_masked_fixture(', 'prove_fixture_any(')
rep('prover::prove_masked_attempt(', 'prove_attempt_any(')
rep('use aspis_r1_cost_probe::{prover, transport::Variant, verifier::View};',
    '''use aspis_r1_cost_probe::{prover, transport::Variant, verifier::View};

// Proof-size candidate (UNPROVED, 2026-10-19): prover and length selection.
#[cfg(feature = "compact-binary")]
fn prove_fixture_any(public: aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>, compiled: &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestMergedC1CompilationV1, _v: Variant, hash: aspis_core::HashFn, seed: &[u8; 32]) -> Result<(Vec<u8>, prover::MaskedFixtureAudit), aspis_r1_cost_probe::verifier::Error> {
    prover::prove_masked_fixture_candidate(public, compiled, hash, seed)
}
#[cfg(not(feature = "compact-binary"))]
fn prove_fixture_any(public: aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>, compiled: &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestMergedC1CompilationV1, v: Variant, hash: aspis_core::HashFn, seed: &[u8; 32]) -> Result<(Vec<u8>, prover::MaskedFixtureAudit), aspis_r1_cost_probe::verifier::Error> {
    prover::prove_masked_fixture(public, compiled, v, hash, seed)
}
#[cfg(feature = "compact-binary")]
fn prove_attempt_any(public: aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>, compiled: &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestMergedC1CompilationV1, _v: Variant, hash: aspis_core::HashFn, attempt: StateOnlyAttemptSecrets, store: &mut DurableStateOnlyMaskNonceStore) -> Result<(Vec<u8>, prover::MaskedFixtureAudit), aspis_r1_cost_probe::verifier::Error> {
    prover::prove_masked_attempt_candidate(public, compiled, hash, attempt, store)
}
#[cfg(not(feature = "compact-binary"))]
fn prove_attempt_any(public: aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>, compiled: &aspis_statement::pool_v1::pair_forest_trace::PoolV1PairForestMergedC1CompilationV1, v: Variant, hash: aspis_core::HashFn, attempt: StateOnlyAttemptSecrets, store: &mut DurableStateOnlyMaskNonceStore) -> Result<(Vec<u8>, prover::MaskedFixtureAudit), aspis_r1_cost_probe::verifier::Error> {
    prover::prove_masked_attempt(public, compiled, v, hash, attempt, store)
}
fn canonical_proof_bytes() -> usize {
    #[cfg(feature = "compact-binary")]
    { aspis_r1_cost_probe::compact::PROOF_BYTES }
    #[cfg(not(feature = "compact-binary"))]
    { View::proof_bytes(Variant::S2) }
}
/// Native candidate checks and per-slot node counts (S2).
#[cfg(feature = "compact-binary")]
fn candidate_native(full_public_bytes: &[u8], proof: &[u8]) -> Result<serde_json::Value> {
    use aspis_r1_cost_probe::{compact, multiproof, verifier::candidate};
    let hash = aspis_core::digest::LegacyHashFn(HOST_HASH);
    let st = decode_pool_v1_pair_forest_terminal_statement_v1(full_public_bytes).map_err(|e| anyhow!("decode ASF8: {e:?}"))?;
    let t0 = std::time::Instant::now();
    let ck = candidate::tx1(st.semantic_public(), full_public_bytes, proof, compact::SPLIT, hash, None).map_err(|e| anyhow!("candidate native tx1: {e:?}"))?;
    candidate::tx2(full_public_bytes, proof, &ck, hash, None).map_err(|e| anyhow!("candidate native tx2: {e:?}"))?;
    candidate::tx2_authenticated(full_public_bytes, proof, &ck, hash, None).map_err(|e| anyhow!("candidate native tx2_authenticated: {e:?}"))?;
    let verify_seconds = t0.elapsed().as_secs_f64();
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
    Ok(serde_json::json!({"native_candidate_tx1_tx2": "accepted", "stored_bytes": proof.len(),
        "queries": queries, "slot_nodes": nodes, "total_nodes": total,
        "variable_length_bytes": compact::FIXED + 32 * total, "native_verify_seconds": verify_seconds}))
}
''')
rep('''        proof_body.len() == View::proof_bytes(Variant::S2),
        "R1 S2 proof body has the wrong canonical length"
    );''', '''        proof_body.len() == canonical_proof_bytes(),
        "R1 S2 proof body has the wrong canonical length"
    );
    if let Ok(path) = std::env::var("R1_PROOF_SIZE_EXPECT_PUBLIC") {
        ensure!(fs::read(&path)? == full_public_bytes, "generated ASF8 differs from {path}");
        eprintln!("PROOF_SIZE_PUBLIC_MATCHES={path}");
    }
    #[cfg(feature = "compact-binary")]
    {
        let native = candidate_native(&full_public_bytes, &proof_body)?;
        eprintln!("PROOF_SIZE_NATIVE={native}");
        if std::env::var("R1_PROOF_SIZE_NATIVE_ONLY").as_deref() == Ok("1") {
            return Ok(());
        }
    }''')
rep('''    let mut svm = LiteSVM::new();''', '''    let mut svm = LiteSVM::new();
    if std::env::var("R1_PROOF_SIZE_UPLOAD_PROBE").as_deref() == Ok("1") {
        // Serialized lifecycle write (tag 5 || u32 offset || chunk) with the
        // payer and the upload authority signing, as `lifecycle_upload`.
        let authority = Keypair::new();
        let target = legacy(Keypair::new().pubkey().to_bytes());
        for version in [TxVersion::V1, TxVersion::V0] {
            let limit = version.target_bytes();
            let mut best = 0;
            for chunk in [0usize, 100, 800, 900, 960] {
                let ix = lifecycle_instruction(verifier_program, target, legacy(authority.pubkey().to_bytes()), lifecycle_write_data(0, &vec![0xa5; chunk]));
                let tx = transaction_with_signers(&svm, &payer, ix, &[&authority], version)?;
                let bytes = wincode::serialize(&tx)?.len();
                eprintln!("PROOF_SIZE_UPLOAD_TX version={} chunk={chunk} serialized={bytes} overhead={}", version.display_name(), bytes - chunk);
            }
            // Largest chunk that fits the limit (overhead is chunk-independent
            // except for the compact-u16 length prefix; search to be exact).
            let mut chunk = 1usize;
            loop {
                let ix = lifecycle_instruction(verifier_program, target, legacy(authority.pubkey().to_bytes()), lifecycle_write_data(0, &vec![0xa5; chunk]));
                let Ok(tx) = transaction_with_signers(&svm, &payer, ix, &[&authority], version) else { break };
                if wincode::serialize(&tx)?.len() > limit { break; }
                best = chunk;
                chunk += 1;
            }
            eprintln!("PROOF_SIZE_UPLOAD_MAX version={} limit={limit} max_chunk={best}", version.display_name());
        }
        return Ok(());
    }''')
src.write_text(s)
print(hashlib.sha256(s.encode()).hexdigest())
