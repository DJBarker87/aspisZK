//! Fixed-coin full-pipeline differential and timing gate. No production entropy.
use aspis_core::digest::LegacyHashFn;
use aspis_prover::{r0_fixture, state_only_entropy::{DurableStateOnlyMaskNonceStore, StateOnlyAttemptSecrets}, HOST_HASH};
use aspis_r1_cost_probe::{prover, transport::Variant, verifier};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{fs, path::Path, time::Instant};

fn main() {
    assert!(!cfg!(debug_assertions));
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 4, "usage: prover_rw_gate fresh-output-dir first-coin count");
    let out = Path::new(&args[1]);
    assert!(!out.exists());
    fs::create_dir_all(out).unwrap();
    let first: u64 = args[2].parse().unwrap();
    let count: u64 = args[3].parse().unwrap();
    for withdrawal in [false, true] {
        let fixture = r0_fixture::prepare(withdrawal);
        let public_bytes = fixture.public().public_bytes().unwrap();
        let name = if withdrawal { "withdrawal" } else { "transfer" };
        for coin in first..first + count {
            let run = out.join(format!("{name}-{coin}"));
            fs::create_dir(&run).unwrap();
            let mut store = DurableStateOnlyMaskNonceStore::open(run.join("ledger")).unwrap();
            let mut callbacks = 0;
            let started = Instant::now();
            let result = prover::prove_masked_retrying_with(fixture.public(), &fixture.compiled,
                Variant::S2, HOST_HASH, &mut store, |attempt| {
                    callbacks += 1;
                    let seed = |domain: &[u8]| HOST_HASH(&[b"PROVER-RW:insecure-fixed-coins", domain,
                        &public_bytes, &coin.to_le_bytes(), &(attempt as u64).to_le_bytes()]);
                    Ok(StateOnlyAttemptSecrets::deterministic_spend_fixture(
                        seed(b"nonce"), seed(b"field"), seed(b"leaf")))
                });
            let seconds = started.elapsed().as_secs_f64();
            let mut row = json!({"fixture":name,"coin":coin,"seconds":seconds,
                "callbacks":callbacks,"workers":16,"entropy":"deterministic fixture only",
                "scope":"complete retrying prover call including durable reservation and P_R1"});
            match result {
                Ok(result) => {
                    assert_eq!(callbacks,result.attempts);
                    let checkpoint = verifier::tx1(fixture.public(), &public_bytes, &result.proof,
                        verifier::SPLIT, LegacyHashFn(HOST_HASH), None).unwrap();
                    verifier::tx2(&public_bytes, &result.proof, &checkpoint, LegacyHashFn(HOST_HASH), None).unwrap();
                    row["status"] = json!("Ok");
                    row["attempts"] = json!(result.attempts);
                    row["proof_sha256"] = json!(format!("{:x}", Sha256::digest(&result.proof)));
                    row["audit"] = json!(format!("{:?}",result.audit));
                    fs::write(run.join("proof.bin"),result.proof).unwrap();
                }
                Err(error) => {row["status"]=json!(format!("{error:?}"));}
            }
            fs::write(run.join("public.bin"),&public_bytes).unwrap();
            fs::write(run.join("result.json"),serde_json::to_vec_pretty(&row).unwrap()).unwrap();
            println!("{row}");
        }
    }
}
