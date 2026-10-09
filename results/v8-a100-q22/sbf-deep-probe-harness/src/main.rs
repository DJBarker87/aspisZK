use std::{env, fs, path::PathBuf, str::FromStr};

use anyhow::{anyhow, bail, Context, Result};
use litesvm::LiteSVM;
use serde_json::json;
use sha2::{Digest, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_sdk_ids::system_program;
use solana_signer::Signer;
use solana_transaction::Transaction;

const HARNESS_VERSION: &str = "aspis-v8-deep-sbf-probe-v1";
const LITESVM_VERSION: &str = "0.16.0";
const AGAVE_RUNTIME_VERSION: &str = "4.2.1";
const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;
const V8_MAX_BODY_BYTES: usize = 39_934;
const EXPECTED_ARTIFACT_BYTES: usize = 182_008;
const EXPECTED_ARTIFACT_SHA256: &str =
    "6dd166e8d57018c6204edbacd73fdb140ebb30b847ad114249f1599913476e0a";
const VERIFIER_ID: &str = "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue";

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn parse_args() -> Result<(PathBuf, PathBuf)> {
    let mut args = env::args().skip(1);
    let artifact = args
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| anyhow!("usage: harness <aspis_verifier.so> <evidence.json>"))?;
    let evidence = args
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| anyhow!("usage: harness <aspis_verifier.so> <evidence.json>"))?;
    if args.next().is_some() {
        bail!("unexpected extra argument");
    }
    Ok((artifact, evidence))
}

fn transaction(
    svm: &mut LiteSVM,
    payer: &Keypair,
    program_id: Address,
    proof: Address,
    mode: u8,
) -> Transaction {
    svm.expire_blockhash();
    Transaction::new_signed_with_payer(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(COMPUTE_UNIT_LIMIT),
            Instruction {
                program_id,
                accounts: vec![AccountMeta::new_readonly(proof, false)],
                data: vec![mode],
            },
        ],
        Some(&payer.pubkey()),
        &[payer],
        svm.latest_blockhash(),
    )
}

fn run_mode(
    svm: &mut LiteSVM,
    payer: &Keypair,
    program_id: Address,
    proof: Address,
    mode: u8,
    name: &str,
) -> Result<serde_json::Value> {
    let tx = transaction(svm, payer, program_id, proof, mode);
    let simulation = svm.simulate_transaction(tx.clone()).map_err(|failed| {
        anyhow!(
            "{name} simulation failed: {:?}\n{}",
            failed.err,
            failed.meta.pretty_logs()
        )
    })?;
    let executed = svm.send_transaction(tx).map_err(|failed| {
        anyhow!(
            "{name} execution failed: {:?}\n{}",
            failed.err,
            failed.meta.pretty_logs()
        )
    })?;
    if simulation.meta != executed {
        bail!("{name}: simulation metadata differed from execution");
    }
    if executed.compute_units_consumed > u64::from(COMPUTE_UNIT_LIMIT) {
        bail!("{name}: compute exceeded configured limit");
    }
    let checksum_log = executed
        .logs
        .iter()
        .find(|line| line.starts_with("Program data: "))
        .cloned()
        .ok_or_else(|| anyhow!("{name}: output checksum log absent"))?;
    Ok(json!({
        "mode": mode,
        "name": name,
        "compute_units": executed.compute_units_consumed,
        "checksum_log": checksum_log,
        "logs": executed.logs,
    }))
}

fn main() -> Result<()> {
    let (artifact_path, evidence_path) = parse_args()?;
    let artifact = fs::read(&artifact_path)
        .with_context(|| format!("read artifact {}", artifact_path.display()))?;
    let artifact_sha256 = sha256_hex(&artifact);
    if artifact.len() != EXPECTED_ARTIFACT_BYTES || artifact_sha256 != EXPECTED_ARTIFACT_SHA256 {
        bail!(
            "artifact mismatch: {} bytes sha256 {}",
            artifact.len(),
            artifact_sha256
        );
    }

    let program_id = Address::from_str(VERIFIER_ID).context("parse verifier id")?;
    let proof = Address::from([0x88; 32]);
    let payer = Keypair::new_from_array([0x41; 32]);
    let mut svm = LiteSVM::new();
    svm.add_program(program_id, &artifact)?;
    svm.airdrop(&payer.pubkey(), 10_000_000)
        .map_err(|failed| anyhow!("fund payer: {:?}", failed.err))?;
    let proof_data = vec![0u8; V8_MAX_BODY_BYTES];
    svm.set_account(
        proof,
        Account {
            lamports: svm.minimum_balance_for_rent_exemption(proof_data.len()),
            data: proof_data,
            owner: system_program::id(),
            executable: false,
            rent_epoch: u64::MAX,
        },
    )
    .map_err(|error| anyhow!("install proof account: {error}"))?;

    let heap_batched = run_mode(
        &mut svm,
        &payer,
        program_id,
        proof,
        0,
        "heap_batched_one_inversion",
    )?;
    let pointwise = run_mode(
        &mut svm,
        &payer,
        program_id,
        proof,
        1,
        "pointwise_88_inversions",
    )?;
    if heap_batched["checksum_log"] != pointwise["checksum_log"] {
        bail!("equivalent implementations returned different checksums");
    }

    let evidence = json!({
        "schema": "aspis-v8-deep-sbf-probe-evidence-v1",
        "harness_version": HARNESS_VERSION,
        "litesvm_version": LITESVM_VERSION,
        "agave_runtime_version": AGAVE_RUNTIME_VERSION,
        "compute_unit_limit": COMPUTE_UNIT_LIMIT,
        "program_id": VERIFIER_ID,
        "proof_body_bytes": V8_MAX_BODY_BYTES,
        "fixture": "all-zero canonical fields with the exact q22 maximum-frontier schedule",
        "artifact": {
            "path": artifact_path.display().to_string(),
            "bytes": artifact.len(),
            "sha256": artifact_sha256,
        },
        "runs": [heap_batched, pointwise],
        "assertions": {
            "both_transactions_accepted": true,
            "checksums_equal": true,
            "no_state_transition_or_cpi": true,
        },
        "boundaries": [
            "This is a verifier-kernel probe, not a complete V8 verifier.",
            "It does not authenticate Merkle openings, fold, settle, or invoke Pool.",
            "The zero body is syntactically canonical but is not a production proof.",
        ],
    });
    fs::write(&evidence_path, serde_json::to_vec_pretty(&evidence)?)
        .with_context(|| format!("write evidence {}", evidence_path.display()))?;
    println!("{}", serde_json::to_string_pretty(&evidence)?);
    Ok(())
}
