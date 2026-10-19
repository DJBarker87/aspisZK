//! LOG D38.3 measurement gate (optimized build only): the prover-side P_R1
//! check on fresh OS-entropy attempts, and the capped retry loop end to end.
//!
//! Part 1: `attempts` independent single attempts (`prove_masked_attempt`,
//! fresh OS secrets, one durable ledger). Each records its wall time, the
//! check's duration split and the one-bit verdict; accepted proofs are
//! verified (strict tx1+tx2 and dense). No challenge, root or failing
//! conjunct is recorded or printed.
//! Part 2: one `prove_masked_retrying` call, timed, then verified.
use aspis_core::digest::LegacyHashFn;
use aspis_prover::{state_only_entropy::{DurableStateOnlyMaskNonceStore, StateOnlyAttemptSecrets}, HOST_HASH};
use aspis_r1_cost_probe::{prover, transport::Variant, verifier, dense};
use serde_json::json;
use std::{path::Path, time::Instant};

fn statement_bytes(fixture: &aspis_prover::r0_fixture::Fixture) -> Vec<u8> {
    aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(&fixture.statement).unwrap().to_vec()
}

fn verify(fixture: &aspis_prover::r0_fixture::Fixture, public_bytes: &[u8], proof: &[u8]) -> bool {
    let Ok(cp) = verifier::tx1(fixture.public(), public_bytes, proof, 11, LegacyHashFn(HOST_HASH), None) else { return false };
    verifier::tx2(public_bytes, proof, &cp, LegacyHashFn(HOST_HASH), None).is_ok()
        && dense::verify(fixture.public(), proof, HOST_HASH).is_ok()
}

fn stats(v: &[f64]) -> serde_json::Value {
    let mut s = v.to_vec();
    s.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = s.len().max(1) as f64;
    json!({"n": s.len(), "mean": s.iter().sum::<f64>() / n, "min": s.first(), "median": s.get(s.len() / 2), "max": s.last()})
}

fn main() {
    assert!(!cfg!(debug_assertions), "run this gate with an optimized profile");
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 4, "usage: r1p_retry_gate <attempts> <fresh-ledger-dir> <out.json>");
    let attempts: usize = args[1].parse().unwrap();
    let ledger_path = Path::new(&args[2]);
    assert!(!ledger_path.exists(), "nonce ledger must be fresh");
    let out = Path::new(&args[3]);
    assert!(!out.exists(), "refusing to overwrite {}", out.display());
    let fixture = aspis_prover::r0_fixture::prepare(false);
    let public_bytes = statement_bytes(&fixture);
    let mut ledger = DurableStateOnlyMaskNonceStore::open(ledger_path).unwrap();
    let _ = prover::take_check_times();

    let mut rows = vec![];
    let (mut wall, mut wall_acc, mut check, mut emit, mut build, mut public_data, mut extracted) = (vec![], vec![], vec![], vec![], vec![], vec![], vec![]);
    let mut accepted = 0usize;
    let mut verified = 0usize;
    for i in 0..attempts {
        let secrets = StateOnlyAttemptSecrets::generate().expect("OS attempt entropy");
        let t = Instant::now();
        let result = prover::prove_masked_attempt(fixture.public(), &fixture.compiled, Variant::S2, HOST_HASH, secrets, &mut ledger);
        let w = t.elapsed().as_secs_f64();
        let times = prover::take_check_times();
        assert_eq!(times.len(), 1, "exactly one P_R1 check per attempt");
        let tm = times[0];
        let total_check = tm.public_data + tm.emit + tm.builders + tm.check;
        let ok = match &result {
            Ok(_) => true,
            Err(verifier::Error::Rejected) => false,
            Err(e) => panic!("attempt {i}: unexpected error {e:?}"),
        };
        let ver = if let Ok((proof, _)) = &result { verify(&fixture, &public_bytes, proof) } else { false };
        if ok {
            accepted += 1;
            wall_acc.push(w);
        }
        if ver {
            verified += 1;
        }
        wall.push(w);
        check.push(total_check);
        public_data.push(tm.public_data);
        emit.push(tm.emit);
        build.push(tm.builders);
        extracted.push(tm.check);
        rows.push(json!({"attempt": i, "accepted": ok, "verified": ver, "attempt_wall_seconds": w,
            "check_seconds": total_check, "check_public_data_seconds": tm.public_data, "check_emit_seconds": tm.emit,
            "check_convert_and_extracted_builders_seconds": tm.builders, "check_extracted_checker_seconds": tm.check,
            "attempt_wall_without_check_seconds": w - total_check}));
        println!("R1P_ATTEMPT {i} accepted={ok} verified={ver} wall={w:.3} check={total_check:.3}");
    }
    let no_check: Vec<f64> = wall.iter().zip(&check).map(|(w, c)| w - c).collect();

    let _ = prover::take_check_times();
    let t = Instant::now();
    let retried = prover::prove_masked_retrying(fixture.public(), &fixture.compiled, Variant::S2, HOST_HASH, &mut ledger).expect("retry loop publishes");
    let retry_wall = t.elapsed().as_secs_f64();
    let retry_checks = prover::take_check_times().len();
    let retry_verified = verify(&fixture, &public_bytes, &retried.proof);
    drop(ledger);
    let reservations = std::fs::read_dir(ledger_path).unwrap().count();
    let report = json!({
        "label": "UNPROVED R1 cost probe: D38.3 prover-side P_R1 check (extracted C3 checker) and retry loop",
        "variant": "S2 (R1)",
        "fixture": "transfer (r0_fixture::prepare(false))",
        "entropy_source": "OS-generated StateOnlyAttemptSecrets, one per attempt",
        "attempts": attempts,
        "accepted": accepted,
        "accept_rate": accepted as f64 / attempts as f64,
        "accepted_proofs_verified_strict_and_dense": verified,
        "attempt_wall_seconds": stats(&wall),
        "accepted_attempt_wall_seconds": stats(&wall_acc),
        "attempt_wall_without_check_seconds": stats(&no_check),
        "check_seconds": stats(&check),
        "check_public_data_seconds": stats(&public_data),
        "check_emit_seconds": stats(&emit),
        "check_convert_and_extracted_builders_seconds": stats(&build),
        "check_extracted_checker_seconds": stats(&extracted),
        "retry_loop": {"wall_seconds": retry_wall, "attempts": retried.attempts, "checks": retry_checks, "verified_strict_and_dense": retry_verified},
        "durable_nonce_reservations": reservations,
        "logged": "verdict bits and durations only; no challenge, root, certificate or failing conjunct",
        "per_attempt": rows,
    });
    std::fs::write(out, serde_json::to_vec_pretty(&report).unwrap()).unwrap();
    println!("R1P_DONE accepted={accepted}/{attempts} verified={verified} retry_attempts={} retry_wall={retry_wall:.3}", retried.attempts);
}
