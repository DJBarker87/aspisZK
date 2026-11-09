//! UNPROVED R1 COST PROBE. Deterministic full-mask fixture acceptance only.
use aspis_core::digest::LegacyHashFn;
use aspis_core::HashFn;
use aspis_prover::HOST_HASH;
use aspis_r1_cost_probe::{prover, transport::Variant, verifier};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{fs, path::Path};

fn sha(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn write_new(path: &Path, value: &serde_json::Value) {
    assert!(!path.exists(), "refusing to overwrite {}", path.display());
    fs::write(path, serde_json::to_string_pretty(value).unwrap() + "\n").unwrap();
}

fn main() {
    assert!(!cfg!(debug_assertions));
    let args: Vec<_> = std::env::args().collect();
    assert!(
        args.len() == 2,
        "usage: masked_fixture_gate <fresh-output-dir>"
    );
    let out = Path::new(&args[1]);
    assert!(!out.exists(), "refusing to overwrite {}", out.display());
    fs::create_dir_all(out).unwrap();
    let hash: HashFn = HOST_HASH;
    let mut records = Vec::new();

    // The adopted format (PREREG-PROOF-SIZE-2) is S2 only.
    for variant in [Variant::S2] {
        for (withdrawal, name) in [(false, "transfer"), (true, "withdrawal")] {
            let fixture = aspis_prover::r0_fixture::prepare(withdrawal);
            let public_bytes =
                aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(
                    &fixture.statement,
                )
                .unwrap();
            let seed = hash(&[
                b"UNPROVED:R1:masked-fixture-gate-seed",
                &public_bytes,
                &[variant.tag()],
            ]);
            let (proof, audit) = prover::prove_masked_fixture(
                fixture.public(),
                &fixture.compiled,
                variant,
                hash,
                &seed,
            )
            .unwrap();

            assert_eq!(audit.c1_columns_inactive_balanced, 16);
            assert_eq!(audit.mask_only_columns_inactive_balanced, 10);
            assert!(audit.d_inactive_balanced);
            assert!(audit.g_inactive_balanced);
            assert!(audit.h1_padding_inactive_balanced);
            assert!(audit.h1_total_balanced);

            let native = verifier::tx1(fixture.public(), &public_bytes, &proof, verifier::SPLIT, LegacyHashFn(hash), None)
                .and_then(|checkpoint| {
                    verifier::tx2(&public_bytes, &proof, &checkpoint, LegacyHashFn(hash), None)
                });
            native.expect("masked fixture native acceptance");
            aspis_r1_cost_probe::dense::verify(fixture.public(), &proof, hash)
                .expect("masked fixture dense acceptance");

            let fixture_dir = out.join(format!(
                "{}-{name}",
                if variant == Variant::S1 { "S1" } else { "S2" }
            ));
            fs::create_dir(&fixture_dir).unwrap();
            let proof_path = fixture_dir.join("proof.bin");
            let public_path = fixture_dir.join("public.bin");
            assert!(!proof_path.exists() && !public_path.exists());
            fs::write(&proof_path, &proof).unwrap();
            fs::write(&public_path, &public_bytes).unwrap();
            let metadata = json!({
                "label": if cfg!(feature = "private-leaf-salts") { "UNPROVED P3 full-mask deterministic fixture" } else { "UNPROVED R1 COST PROBE; deterministic insecure masked fixture" },
                "variant": if variant == Variant::S1 { "S1" } else { "S2" },
                "fixture": name,
                "entropy": if cfg!(feature = "private-leaf-salts") { "deterministic fixture-only nonce, field entropy, and leaf-salt seed; not OS entropy" } else { "deterministic fixture-only nonce, field entropy, and leaf seed; not production entropy" },
                "mask_binding": if cfg!(feature = "private-leaf-salts") { "P3 private-attempt binding; UNPROVED protocol" } else { "host-only public derivation; not a production transcript binding" },
                "native_acceptance": true,
                "dense_acceptance": true,
                "mask_audit": {
                    "c1_columns_inactive_balanced": audit.c1_columns_inactive_balanced,
                    "mask_only_columns_inactive_balanced": audit.mask_only_columns_inactive_balanced,
                    "d_inactive_balanced": audit.d_inactive_balanced,
                    "g_inactive_balanced": audit.g_inactive_balanced,
                    "h1_padding_inactive_balanced": audit.h1_padding_inactive_balanced,
                    "h1_total_balanced": audit.h1_total_balanced,
                },
                "proof_bytes": proof.len(),
                "proof_sha256": sha(&proof),
                "public_bytes": public_bytes.len(),
                "public_sha256": sha(&public_bytes),
            });
            write_new(&fixture_dir.join("fixture.json"), &metadata);
            records.push(metadata);
            println!(
                "{} {name}: native and dense acceptance; balanced full-mask fixture",
                if variant == Variant::S1 { "S1" } else { "S2" }
            );
        }
    }

    #[cfg(feature = "private-leaf-salts")]
    {
        let fixture = aspis_prover::r0_fixture::prepare(false);
        let public_bytes = aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(
            &fixture.statement,
        ).unwrap();
        let nonce = hash(&[b"UNPROVED:R1:P3:nonce-reuse-test", &public_bytes]);
        let context = aspis_core::state_only_hiding::StateOnlyHidingContext::pool_v1_pair_forest_v1(
            hash(&[&public_bytes]), nonce,
        );
        let binding = hash(&[
            b"UNPROVED:R1:P3:PRIVATE-ATTEMPT",
            &public_bytes,
            &[Variant::S1.tag()],
            &context.encode(),
        ]);
        let field_entropy = hash(&[b"UNPROVED:R1:P3:nonce-reuse-field", &public_bytes]);
        let leaf_seed = hash(&[b"UNPROVED:R1:P3:nonce-reuse-leaf", &public_bytes]);
        let mut store = aspis_prover::state_only_hiding::InMemoryStateOnlyMaskNonceStore::default();
        let first = aspis_prover::state_only_entropy::StateOnlyAttemptSecrets::deterministic_spend_fixture(
            nonce, field_entropy, leaf_seed,
        );
        first.reserve_and_build_pool_v1_pair_forest_mask_material_v1(
            hash, binding, context, &mut store,
        ).expect("first reservation builds mask material");
        let replay = aspis_prover::state_only_entropy::StateOnlyAttemptSecrets::deterministic_spend_fixture(
            nonce, field_entropy, leaf_seed,
        );
        assert!(matches!(
            replay.reserve_and_build_pool_v1_pair_forest_mask_material_v1(hash, binding, context, &mut store),
            Err(aspis_prover::state_only_hiding::StateOnlyMaskBuildError::ReusedMaskNonce),
        ), "replayed nonce is rejected before a second proof's mask material exists");
    }

    write_new(
        &out.join("masked-fixture-gate.json"),
        &json!({
            "label": if cfg!(feature = "private-leaf-salts") { "UNPROVED P3 full-mask deterministic fixtures" } else { "UNPROVED R1 COST PROBE; deterministic insecure masked fixtures" },
            "fixture_count": records.len(),
            "fixtures": records,
        }),
    );
}
