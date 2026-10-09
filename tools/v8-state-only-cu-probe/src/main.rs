//! Build-host-only reference verifier measurement, never a network client.
use anyhow::{anyhow, ensure, Result};
use aspis_core::{field::M31, state_only_prefix::STATE_ONLY_RATE512_SHAPE};
use aspis_prover::{
    state_only_candidate_prefix::StateOnlyPowMode,
    state_only_hiding::InMemoryStateOnlyMaskNonceStore,
    state_only_proof::build_hiding_atomic_state_only_proof_v3, HOST_HASH,
};
use aspis_statement::{
    atomic_state_only_trace::atomic_merkle_root_v3, derive_nullifier, derive_owner_key,
    encode_atomic_payment_statement_v4, note_commitment, output_commitment,
    verify_atomic_state_only_candidate_unmined_for_diagnostics_v3,
    verify_atomic_state_only_candidate_v3, AtomicPaymentStatementV4, Digest, MerklePath,
    SpendPublic, SpendWitness,
};
use litesvm::LiteSVM;
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{account_meta::AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_message::{v1, VersionedMessage};
use solana_signer::Signer;
use solana_transaction::{versioned::VersionedTransaction, Transaction};
use std::{env, fs, path::Path, time::Instant};

const LABEL: &str = "unmined diagnostic path (PoW rejection disabled)";
const LIMIT: u32 = 1_400_000;
const TAG: u8 = 240;

fn sha(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn write_json(path: &Path, value: &Value) -> Result<()> {
    fs::write(path, format!("{}\n", serde_json::to_string_pretty(value)?))?;
    Ok(())
}
fn digest(seed: u32) -> Digest {
    core::array::from_fn(|i| M31(seed + 17 * i as u32))
}

// Same deterministic witness as atomic_state_only_full_proof.rs; private fixture only.
fn fixture(dir: &Path) -> Result<()> {
    fs::create_dir_all(dir)?;
    let nullifier_key = digest(101);
    let input_salt = digest(301);
    let output_salt = digest(501);
    let output_owner_key = digest(701);
    let asset_id = M31(17);
    let witness = SpendWitness {
        nullifier_key,
        input_salt,
        output_salt,
        output_owner_key,
        input_asset_id: asset_id,
        value: 1_000_000,
        value_out: 999_999,
        merkle_path: MerklePath {
            siblings: (0..20).map(|level| digest(1_000 + 31 * level)).collect(),
            index: 0x5_a5a5,
        },
    };
    let input = note_commitment(
        &derive_owner_key(&nullifier_key),
        witness.value,
        asset_id,
        &input_salt,
    );
    let output = output_commitment(&output_owner_key, witness.value_out, asset_id, &output_salt);
    let statement = AtomicPaymentStatementV4 {
        pool: [0x5a; 32],
        sequence: 73,
        spend: SpendPublic {
            anchor: atomic_merkle_root_v3(input, &witness.merkle_path)
                .map_err(|e| anyhow!("{e:?}"))?,
            nullifier: derive_nullifier(&nullifier_key, &input_salt),
            output_commitment: output,
            asset_id,
            fee: 1,
        },
        output_anchor: atomic_merkle_root_v3(output, &witness.merkle_path)
            .map_err(|e| anyhow!("{e:?}"))?,
        deployment_domain: [0x5d; 32],
    };
    let start = Instant::now();
    let proof = build_hiding_atomic_state_only_proof_v3(
        &statement,
        &witness,
        [20; 32],
        [0xd3; 32],
        &mut InMemoryStateOnlyMaskNonceStore::default(),
        STATE_ONLY_RATE512_SHAPE,
        HOST_HASH,
        StateOnlyPowMode::UnminedZero,
    )
    .map_err(|e| anyhow!("fixture: {e:?}"))?;
    let build_seconds = start.elapsed().as_secs_f64();
    ensure!(!proof.pow_valid);
    verify_atomic_state_only_candidate_unmined_for_diagnostics_v3(
        &proof.bytes,
        &statement,
        HOST_HASH,
        None,
    )
    .map_err(|e| anyhow!("host diagnostic verify: {e:?}"))?;
    let strict_error = verify_atomic_state_only_candidate_v3(&proof.bytes, &statement, HOST_HASH)
        .expect_err("unmined fixture must not pass strict acceptance");
    let public = encode_atomic_payment_statement_v4(&statement).map_err(|e| anyhow!("{e:?}"))?;
    fs::write(dir.join("rate512-q16.proof.bin"), &proof.bytes)?;
    fs::write(dir.join("rate512-q16.public.bin"), public)?;
    write_json(
        &dir.join("fixture.json"),
        &json!({
            "label": LABEL, "shape": "STATE_ONLY_RATE512_SHAPE", "profile_id": 20,
            "query_count": 16, "log_rows": 10, "log_blowup": 9, "domain_points": 524288,
            "query_fibres": 131072, "batch_grinding_bits": 36,
            "fold_grinding_bits": [39,35,31,27], "final_grinding_bits": 36,
            "proof_bytes": proof.bytes.len(), "proof_sha256": sha(&proof.bytes),
            "public_bytes": public.len(), "public_sha256": sha(&public),
            "host_diagnostic_accepted": true, "strict_host_rejection": format!("{strict_error:?}"),
            "fixture_build_wall_seconds": build_seconds,
            "source_revision": env::var("ASPIS_SOURCE_REVISION")?,
        }),
    )?;
    Ok(())
}

fn markers(logs: &[String]) -> Vec<Value> {
    let mut result = Vec::new();
    let mut name = None;
    let mut previous = None;
    for log in logs {
        if let Some(label) = log.strip_prefix("Program log: v8-state-only:") {
            name = Some(label.to_string());
        } else if let Some(text) = log.strip_prefix("Program consumption: ") {
            if let (Some(label), Some(remaining)) = (
                name.take(),
                text.split_whitespace()
                    .next()
                    .and_then(|s| s.parse::<u64>().ok()),
            ) {
                result.push(json!({"phase": label, "remaining_cu": remaining,
                    "delta_from_previous_cu": previous.map(|p: u64| p - remaining)}));
                previous = Some(remaining);
            }
        }
    }
    result
}

fn measure(elf_path: &Path, fixture_dir: &Path, out: &Path, reject: bool) -> Result<()> {
    fs::create_dir_all(out)?;
    let elf = fs::read(elf_path)?;
    let mut proof = fs::read(fixture_dir.join("rate512-q16.proof.bin"))?;
    let public = fs::read(fixture_dir.join("rate512-q16.public.bin"))?;
    ensure!(public.len() == 216);
    let fixture: Value = serde_json::from_slice(&fs::read(fixture_dir.join("fixture.json"))?)?;
    ensure!(fixture["proof_sha256"] == sha(&proof));
    ensure!(fixture["public_sha256"] == sha(&public));
    let original_proof_sha256 = sha(&proof);
    let mutation = if reject {
        // The suffix begins with a u16 leaf count, then slot-major C1 leaves.
        // Flip only the low bit of the first opened leaf's first M31 limb.
        let offset = aspis_core::state_only_prefix::STATE_ONLY_PREFIX_OFFSETS.openings_start + 2;
        ensure!(u16::from_le_bytes(proof[offset - 2..offset].try_into()?) > 0);
        let before = proof[offset];
        proof[offset] ^= 1;
        let limb_after = u32::from_le_bytes(proof[offset..offset + 4].try_into()?);
        ensure!(
            limb_after < aspis_core::field::P,
            "mutation must remain canonical"
        );
        Some(
            json!({"kind": "first opened C1 leaf, first M31 limb, low-bit flip",
            "proof_byte_offset": offset, "byte_before": before, "byte_after": proof[offset],
            "changed_bytes": 1, "limb_after": limb_after, "canonical_after": true,
            "layout_source": "crates/aspis-prover/src/circle_candidate_openings.rs:250-252"}),
        )
    } else {
        None
    };
    let program = Address::new_from_array([0x81; 32]);
    let proof_key = Address::new_from_array([0x82; 32]);
    // The in-memory payer has no network funds/authority. Persist its key securely anyway.
    let key_path = fixture_dir.join("litesvm-payer.json");
    let payer = if key_path.exists() {
        let bytes: Vec<u8> = serde_json::from_slice(&fs::read(&key_path)?)?;
        Keypair::try_from(bytes.as_slice())?
    } else {
        use std::io::Write;
        use std::os::unix::fs::OpenOptionsExt;
        let payer = Keypair::new();
        fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&key_path)?
            .write_all(serde_json::to_string(&payer.to_bytes().to_vec())?.as_bytes())?;
        payer
    };
    let mut account = vec![0u8; 40];
    account[..4].copy_from_slice(b"ASPU");
    account[4..8].copy_from_slice(&(proof.len() as u32).to_le_bytes());
    account.extend_from_slice(&proof);
    let mut data = vec![TAG];
    data.extend_from_slice(&public);
    let ix = Instruction {
        program_id: program,
        accounts: vec![AccountMeta::new_readonly(proof_key, false)],
        data,
    };
    let mut first = None;
    for run in 1..=if reject { 1 } else { 5 } {
        let filename = if reject {
            "rate512-q16-reject-1.json".to_owned()
        } else {
            format!("rate512-q16-run-{run}.json")
        };
        let start = Instant::now();
        let mut svm = LiteSVM::new();
        svm.airdrop(&payer.pubkey(), 1_000_000_000)
            .map_err(|e| anyhow!("airdrop: {e:?}"))?;
        if let Err(error) = svm.add_program(program, &elf) {
            write_json(
                &out.join(&filename),
                &json!({
                    "label": LABEL, "run": run, "load_error": format!("{error:?}"),
                    "elf_sha256": sha(&elf), "verifier_cu": null,
                }),
            )?;
            return Err(anyhow!("SBF load failed: {error:?}"));
        }
        svm.set_account(
            proof_key,
            Account {
                lamports: 100_000_000,
                data: account.clone(),
                owner: program,
                executable: false,
                rent_epoch: 0,
            },
        )?;
        let instructions = [
            ComputeBudgetInstruction::set_compute_unit_limit(LIMIT),
            ComputeBudgetInstruction::request_heap_frame(256 * 1024),
            ix.clone(),
        ];
        let tx = Transaction::new_signed_with_payer(
            &instructions,
            Some(&payer.pubkey()),
            &[&payer],
            svm.latest_blockhash(),
        );
        // Exact proposed verifier-only TxV1 bytes, independently serialized. CU executes legacy.
        let message = v1::Message::try_compile_with_config(
            &payer.pubkey(),
            &[ix.clone()],
            svm.latest_blockhash(),
            v1::TransactionConfig::empty()
                .with_priority_fee(0)
                .with_compute_unit_limit(LIMIT)
                .with_loaded_accounts_data_size_limit(64 * 1024 * 1024)
                .with_heap_size(256 * 1024),
        )?;
        let txv1 = VersionedTransaction::try_new(VersionedMessage::V1(message), &[&payer])?;
        let txv1_bytes = wincode::serialize(&txv1)?.len();
        ensure!(txv1_bytes <= 4096);
        let simulation = match svm.simulate_transaction(tx.clone()) {
            Ok(r) => (None, r.meta),
            Err(r) => (Some(format!("{:?}", r.err)), r.meta),
        };
        let execution = match svm.send_transaction(tx) {
            Ok(r) => (None, r),
            Err(r) => (Some(format!("{:?}", r.err)), r.meta),
        };
        let agree = simulation.0 == execution.0
            && simulation.1.compute_units_consumed == execution.1.compute_units_consumed
            && simulation.1.logs == execution.1.logs;
        let unchanged = svm.get_account(&proof_key).unwrap().data == account;
        let phase_markers = markers(&execution.1.logs);
        let verifier_cu = execution.1.logs.iter().find_map(|line| {
            line.strip_prefix(&format!("Program {program} consumed "))?
                .split_whitespace()
                .next()?
                .parse::<u64>()
                .ok()
        });
        let signature = (execution.0.clone(), verifier_cu, phase_markers.clone());
        let identical = first.as_ref().map_or(true, |f| f == &signature);
        first.get_or_insert(signature);
        let record = json!({
            "schema": "aspis.v8-state-only-cu.run.v1", "label": LABEL, "run": run,
            "shape": "STATE_ONLY_RATE512_SHAPE", "query_count": 16, "proof_bytes": proof.len(),
            "proof_sha256": sha(&proof), "public_sha256": sha(&public), "elf_sha256": sha(&elf),
            "original_proof_sha256": original_proof_sha256, "mutation": mutation,
            "expected_rejection": reject,
            "elf_source_revision": env::var("ASPIS_ELF_SOURCE_REVISION").unwrap_or(env::var("ASPIS_SOURCE_REVISION")?),
            "source_revision": env::var("ASPIS_SOURCE_REVISION")?,
            "runtime": {"litesvm": "0.16.0", "agave": "4.2.1", "limit_cu": LIMIT,
                "heap_bytes": 262144, "execution_wire": "legacy", "release_build": !cfg!(debug_assertions)},
            "txv1_bytes": txv1_bytes, "txv1_headroom_bytes": 4096 - txv1_bytes,
            "txv1_scope": "serialized signed verifier-only proposal; not executed as TxV1",
            "simulation": {"error": simulation.0, "cu": simulation.1.compute_units_consumed,
                "logs": simulation.1.logs},
            "execution": {"error": execution.0, "cu": execution.1.compute_units_consumed,
                "logs": execution.1.logs},
            "simulation_execution_agree": agree, "identical_to_first_run": identical,
            "proof_account_unchanged": unchanged, "verifier_cu": verifier_cu,
            "verifier_completed": execution.0.is_none(), "phase_markers": phase_markers,
            "wall_seconds": start.elapsed().as_secs_f64(),
            "excluded": ["pool CPI", "receipts", "settlement", "proof upload", "network execution"],
        });
        write_json(&out.join(&filename), &record)?;
        ensure!(
            agree && unchanged && identical,
            "measurement disagreement: run {run}"
        );
        if reject {
            ensure!(
                execution.0.as_deref() == Some("InstructionError(2, InvalidInstructionData)"),
                "expected checked verifier rejection, got {:?}",
                execution.0
            );
            ensure!(
                phase_markers
                    .iter()
                    .any(|p| p["phase"] == "relation-final-polynomial")
                    && !phase_markers
                        .iter()
                        .any(|p| p["phase"] == "merkle-openings"),
                "corrupted leaf must reach and fail opening authentication"
            );
        }
        println!(
            "run {run}: {LABEL}; verifier CU {verifier_cu:?}; error {:?}",
            execution.0
        );
    }
    Ok(())
}

fn main() -> Result<()> {
    ensure!(!cfg!(debug_assertions), "release build required");
    let args: Vec<_> = env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("fixture") if args.len() == 3 => fixture(Path::new(&args[2])),
        Some("measure" | "reject") if args.len() == 5 => measure(
            Path::new(&args[2]),
            Path::new(&args[3]),
            Path::new(&args[4]),
            args[1] == "reject",
        ),
        _ => Err(anyhow!(
            "usage: v8-state-only-cu-probe fixture DIR | measure|reject ELF FIXTURE_DIR RESULTS_DIR"
        )),
    }
}
