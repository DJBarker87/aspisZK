//! pv-aspis-rewrite-20261111, gate B and gate C driver. A test on fixtures, not a proof.
//!
//! Prints one line per (operation, seed) with the sha256 of the proof the deterministic
//! insecure fixture prover writes in the pinned format and of the same proof re-packed
//! into the summed format. Two builds of this tool from two source trees prove the same
//! bytes on these inputs exactly when the printed tables are equal.
//!
//! usage:
//!   pv_bytes_gate table <first-seed> <count> [<ledger-root>]
//!       FIXTURE lines: `prover::prove_masked_fixture` for transfer and withdrawal and each
//!       seed byte in first-seed..first-seed+count. With the feature `r1p-check` the public
//!       check runs inside the prover, so a seed whose challenges fail it prints
//!       `result=err:Rejected` (that is the single-attempt failure path).
//!       RETRY lines (feature `r1p-check`, and only when <ledger-root> is given): the retry
//!       loop `prover::prove_masked_retrying_with` with attempt secrets derived from the seed
//!       and the attempt number, on a fresh durable nonce ledger under <ledger-root> (which
//!       must not exist: a nonce ledger is never reused). `attempts` is the number of attempts
//!       entered, `checks` the number of check timings the call left for `take_check_times`.
//!       No timing value is printed in this mode, so the output is comparable byte for byte.
//!   pv_bytes_gate time <seed> <iterations>
//!       TIME lines: wall seconds of `prove_masked_fixture` alone (fixture preparation is
//!       outside the interval), per operation and iteration.
use aspis_core::digest::LegacyHashFn;
use aspis_prover::{r0_fixture, HOST_HASH};
use aspis_r1_cost_probe::{prover, transport::Variant, verifier::candidate::fused};
use sha2::{Digest, Sha256};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn sha(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn describe(fixture: &r0_fixture::Fixture, proof: &[u8]) -> String {
    match fused::to_summed_format(fixture.statement.semantic_public(), proof, LegacyHashFn(HOST_HASH)) {
        Ok(packed) => format!(
            "pinned_len={} pinned_sha256={} packed_len={} packed_sha256={}",
            proof.len(),
            sha(proof),
            packed.len(),
            sha(&packed)
        ),
        Err(e) => format!("pinned_len={} pinned_sha256={} packed=err:{e:?}", proof.len(), sha(proof)),
    }
}

const OPERATIONS: [(&str, bool); 2] = [("transfer", false), ("withdrawal", true)];

#[cfg(feature = "r1p-check")]
fn retry_rows(root: &std::path::Path, first: u8, count: u8) {
    use aspis_prover::state_only_entropy::{DurableStateOnlyMaskNonceStore, StateOnlyAttemptSecrets};
    assert!(!root.exists(), "refusing to reuse a nonce ledger root: {}", root.display());
    for (name, withdrawal) in OPERATIONS {
        let fixture = r0_fixture::prepare(withdrawal);
        for seed in first..first + count {
            let mut ledger = DurableStateOnlyMaskNonceStore::open(root.join(format!("{name}-{seed}"))).expect("ledger");
            let secret = |domain: &[u8], k: usize| -> [u8; 32] {
                let mut d = Sha256::new();
                d.update(b"pv-bytes-gate retry v1");
                d.update(domain);
                d.update(name.as_bytes());
                d.update([seed, k as u8]);
                d.finalize().into()
            };
            let mut entered = Vec::new();
            let _ = prover::take_check_times();
            let result = prover::prove_masked_retrying_with(
                fixture.public(),
                &fixture.compiled,
                Variant::S2,
                HOST_HASH,
                &mut ledger,
                |k| {
                    entered.push(k);
                    Ok(StateOnlyAttemptSecrets::deterministic_spend_fixture(
                        secret(b"nonce", k),
                        secret(b"field", k),
                        secret(b"leaf", k),
                    ))
                },
            );
            let checks = prover::take_check_times().len();
            let entered: Vec<String> = entered.iter().map(|k| k.to_string()).collect();
            match result {
                Ok(retried) => println!(
                    "RETRY op={name} seed={seed} result=ok attempts={} entered={} checks={checks} {}",
                    retried.attempts,
                    entered.join("."),
                    describe(&fixture, &retried.proof)
                ),
                Err(e) => println!(
                    "RETRY op={name} seed={seed} result=err:{e:?} entered={} checks={checks}",
                    entered.join(".")
                ),
            }
            // A second call on the same ledger with the same first nonce must fail closed
            // (duplicate reservation) after entering exactly one attempt.
            let mut again = Vec::new();
            let duplicate = prover::prove_masked_retrying_with(
                fixture.public(),
                &fixture.compiled,
                Variant::S2,
                HOST_HASH,
                &mut ledger,
                |k| {
                    again.push(k);
                    Ok(StateOnlyAttemptSecrets::deterministic_spend_fixture(
                        secret(b"nonce", k),
                        secret(b"field", k),
                        secret(b"leaf", k),
                    ))
                },
            );
            let checks = prover::take_check_times().len();
            println!(
                "RETRY-DUPLICATE op={name} seed={seed} result={} entered={} checks={checks}",
                match duplicate {
                    Ok(_) => "ok".to_string(),
                    Err(e) => format!("err:{e:?}"),
                },
                again.len()
            );
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: pv_bytes_gate table <first-seed> <count> [<ledger-root>] | time <seed> <iterations>";
    match args.get(1).map(String::as_str) {
        Some("table") => {
            let first: u8 = args.get(2).expect(usage).parse().expect("first seed");
            let count: u8 = args.get(3).expect(usage).parse().expect("count");
            println!("PV_BYTES_GATE table first={first} count={count} r1p_check={}", cfg!(feature = "r1p-check"));
            for (name, withdrawal) in OPERATIONS {
                let fixture = r0_fixture::prepare(withdrawal);
                for seed in first..first + count {
                    #[cfg(feature = "r1p-check")]
                    let _ = prover::take_check_times();
                    let result = prover::prove_masked_fixture(
                        r0_fixture::statement_public(&fixture.statement),
                        &fixture.compiled,
                        Variant::S2,
                        HOST_HASH,
                        &[seed; 32],
                    );
                    #[cfg(feature = "r1p-check")]
                    let checks = prover::take_check_times().len().to_string();
                    #[cfg(not(feature = "r1p-check"))]
                    let checks = "na".to_string();
                    match result {
                        Ok((proof, audit)) => println!(
                            "FIXTURE op={name} seed={seed} result=ok checks={checks} audit={}.{}.{}.{}.{}.{} {}",
                            audit.c1_columns_inactive_balanced,
                            audit.mask_only_columns_inactive_balanced,
                            audit.d_inactive_balanced,
                            audit.g_inactive_balanced,
                            audit.h1_padding_inactive_balanced,
                            audit.h1_total_balanced,
                            describe(&fixture, &proof)
                        ),
                        Err(e) => println!("FIXTURE op={name} seed={seed} result=err:{e:?} checks={checks}"),
                    }
                }
            }
            #[cfg(feature = "r1p-check")]
            if let Some(root) = args.get(4) {
                retry_rows(std::path::Path::new(root), first, count);
            }
            #[cfg(not(feature = "r1p-check"))]
            println!("RETRY not built (feature r1p-check off)");
        }
        Some("time") => {
            let seed: u8 = args.get(2).expect(usage).parse().expect("seed");
            let iterations: usize = args.get(3).expect(usage).parse().expect("iterations");
            for (name, withdrawal) in OPERATIONS {
                let fixture = r0_fixture::prepare(withdrawal);
                for i in 0..iterations {
                    let start = std::time::Instant::now();
                    let result = prover::prove_masked_fixture(
                        r0_fixture::statement_public(&fixture.statement),
                        &fixture.compiled,
                        Variant::S2,
                        HOST_HASH,
                        &[seed; 32],
                    );
                    let seconds = start.elapsed().as_secs_f64();
                    println!(
                        "TIME op={name} seed={seed} iteration={i} seconds={seconds:.6} result={}",
                        match &result {
                            Ok(_) => "ok".to_string(),
                            Err(e) => format!("err:{e:?}"),
                        }
                    );
                }
            }
        }
        _ => panic!("{usage}"),
    }
}
