//! UNPROVED P3 secure-source host API gate. Preserves its durable nonce ledger.
use aspis_core::digest::LegacyHashFn;
use aspis_core::HashFn;
use aspis_prover::{
    state_only_entropy::{DurableStateOnlyMaskNonceStore, StateOnlyAttemptSecrets},
    HOST_HASH,
};
use aspis_r1_cost_probe::{prover, transport::Variant, verifier, dense};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{fs, path::Path};

fn sha(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn write_new(path: &Path, bytes: &[u8]) {
    assert!(!path.exists(), "refusing to overwrite {}", path.display());
    fs::write(path, bytes).unwrap();
}

fn statement_bytes(fixture: &aspis_prover::r0_fixture::Fixture) -> Vec<u8> {
    aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(
        &fixture.statement,
    )
    .unwrap()
    .to_vec()
}

fn main() {
    assert!(!cfg!(debug_assertions), "run this gate with an optimized profile");
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 3, "usage: secure_attempt_gate <fresh-evidence-dir> <fresh-ledger-dir>");
    let evidence = Path::new(&args[1]);
    let ledger_path = Path::new(&args[2]);
    assert!(!evidence.exists(), "refusing to overwrite {}", evidence.display());
    assert!(!ledger_path.exists(), "nonce ledger must be fresh: {}", ledger_path.display());
    fs::create_dir_all(evidence).unwrap();

    let fixture = aspis_prover::r0_fixture::prepare(false);
    let public_bytes = statement_bytes(&fixture);
    let hash: HashFn = HOST_HASH;
    let first_attempt = StateOnlyAttemptSecrets::generate().expect("OS attempt entropy");
    let public_nonce = first_attempt.mask_nonce();
    let mut ledger = DurableStateOnlyMaskNonceStore::open(ledger_path).unwrap();
    let (proof, audit) = prover::prove_masked_attempt(
        fixture.public(), &fixture.compiled, Variant::S2, hash, first_attempt, &mut ledger,
    ).expect("first OS-generated P3 proof");

    assert_eq!(audit.c1_columns_inactive_balanced, 16);
    assert_eq!(audit.mask_only_columns_inactive_balanced, 10);
    assert!(audit.d_inactive_balanced && audit.g_inactive_balanced);
    assert!(audit.h1_padding_inactive_balanced && audit.h1_total_balanced);
    let checkpoint = verifier::tx1(fixture.public(), &public_bytes, &proof, 11, LegacyHashFn(hash), None)
        .expect("strict first stage");
    verifier::tx2(&public_bytes, &proof, &checkpoint, LegacyHashFn(hash), None)
        .expect("strict second stage");
    verifier::tx2_authenticated(&public_bytes, &proof, &checkpoint, LegacyHashFn(hash), None)
        .expect("authenticated-checkpoint second stage");
    dense::verify(fixture.public(), &proof, hash).expect("independent dense verifier");

    write_new(&evidence.join("r1-s2-proof.bin"), &proof);
    write_new(&evidence.join("r1-s2-public.bin"), &public_bytes);
    drop(ledger);
    let mut reopened = DurableStateOnlyMaskNonceStore::open(ledger_path).unwrap();
    let replay_same = StateOnlyAttemptSecrets::generate_for_mask_nonce(public_nonce)
        .expect("fresh OS entropy for repeated public nonce");
    assert!(matches!(
        prover::prove_masked_attempt(
            fixture.public(), &fixture.compiled, Variant::S2, hash, replay_same, &mut reopened,
        ),
        Err(verifier::Error::Semantic),
    ), "reopened durable ledger rejects same-statement nonce before proof construction");

    let other_fixture = aspis_prover::r0_fixture::prepare(true);
    let other_public = statement_bytes(&other_fixture);
    assert_ne!(other_public, public_bytes, "cross-statement replay needs distinct public bytes");
    let replay_cross = StateOnlyAttemptSecrets::generate_for_mask_nonce(public_nonce)
        .expect("fresh OS entropy for cross-statement repeated public nonce");
    assert!(matches!(
        prover::prove_masked_attempt(
            other_fixture.public(), &other_fixture.compiled, Variant::S2, hash, replay_cross, &mut reopened,
        ),
        Err(verifier::Error::Semantic),
    ), "durable nonce ledger rejects reuse across statements before proof construction");

    let reservations = fs::read_dir(ledger_path).unwrap().count();
    assert_eq!(reservations, 1, "failed replays must not replace or remove the original reservation");
    fs::write(
        evidence.join("secure-attempt-gate.json"),
        serde_json::to_vec_pretty(&json!({
            "label": "UNPROVED P3 full-mask secure-source API experiment; fresh entropy alone does not establish zero knowledge",
            "variant": "S2",
            "fixture": "transfer",
            "entropy_source": "OS-generated StateOnlyAttemptSecrets",
            "ledger": "durable and retained at the caller-supplied path",
            "strict_acceptance": true,
            "authenticated_checkpoint_acceptance": true,
            "dense_acceptance": true,
            "mask_audit": {
                "c1_columns_inactive_balanced": audit.c1_columns_inactive_balanced,
                "mask_only_columns_inactive_balanced": audit.mask_only_columns_inactive_balanced,
                "d_inactive_balanced": audit.d_inactive_balanced,
                "g_inactive_balanced": audit.g_inactive_balanced,
                "h1_padding_inactive_balanced": audit.h1_padding_inactive_balanced,
                "h1_total_balanced": audit.h1_total_balanced
            },
            "proof_bytes": proof.len(),
            "proof_sha256": sha(&proof),
            "public_bytes": public_bytes.len(),
            "public_sha256": sha(&public_bytes),
            "replay_same_statement_rejected": true,
            "replay_cross_statement_rejected": true,
            "mask_nonce_logged": false
        })).unwrap(),
    ).unwrap();
    println!("P3 secure-source proof accepted by strict, authenticated-checkpoint, and dense verifiers; both nonce replays rejected");
}
