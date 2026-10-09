//! Build-host-only reference verifier measurement, never a network client.
use anyhow::{anyhow, ensure, Result};
use litesvm::LiteSVM;
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};
use solana_account::Account;
use solana_address::Address;
use solana_compute_budget::compute_budget::ComputeBudget;
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_instruction::{account_meta::AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_message::{v1, VersionedMessage};
use solana_signer::Signer;
use solana_transaction::{versioned::VersionedTransaction, Transaction};
use std::{env, fs, path::Path, time::Instant};

const LIMIT: u32 = 1_400_000;
const TAG: u8 = 241;

#[derive(Clone, Copy)]
struct Profile {
    stem: &'static str,
}
impl Profile {
    fn parse(name: Option<&String>) -> Result<Self> {
        Ok(Self {
            stem: match name.map(String::as_str).unwrap_or("transfer") {
                "transfer" => "transfer",
                "withdrawal" => "withdrawal",
                other => return Err(anyhow!("unknown variant {other}")),
            },
        })
    }
}

fn sha(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn write_json(path: &Path, value: &Value) -> Result<()> {
    fs::write(path, format!("{}\n", serde_json::to_string_pretty(value)?))?;
    Ok(())
}
fn fixture(dir: &Path, profile: Profile) -> Result<()> {
    fs::create_dir_all(dir)?;
    let f = aspis_prover::r0_fixture::prepare(profile.stem == "withdrawal");
    let start = Instant::now();
    let proof = f.prove().map_err(|e| anyhow!("prove: {e:?}"))?;
    let prover_seconds = start.elapsed().as_secs_f64();
    // Linux VmHWM is sampled before native verification, so verifier work
    // cannot inflate the prover-process peak. Includes fixture preparation.
    let prover_process_peak_rss_bytes = fs::read_to_string("/proc/self/status")?
        .lines()
        .find_map(|line| {
            line.strip_prefix("VmHWM:")
                .and_then(|v| v.split_whitespace().next()?.parse::<u64>().ok())
        })
        .ok_or_else(|| anyhow!("missing Linux VmHWM"))?
        * 1024;

    let start = Instant::now();
    let checked = aspis_statement::r0::r0_verify(f.public(), &proof, aspis_prover::HOST_HASH, None)
        .map_err(|e| anyhow!("verify: {e:?}"))?;
    let verifier_seconds = start.elapsed().as_secs_f64();
    ensure!(
        aspis_statement::r0::Proof::parse(&proof)
            .unwrap()
            .encode()
            .unwrap()
            == proof
    );
    let public =
        aspis_statement::pool_v1::encode_pool_v1_pair_forest_terminal_statement_v1(&f.statement)
            .map_err(|e| anyhow!("public: {e:?}"))?;
    fs::write(dir.join(format!("{}.proof.bin", profile.stem)), &proof)?;
    fs::write(dir.join(format!("{}.public.bin", profile.stem)), &public)?;
    let metadata = json!({"schema":"aspis.r0-e2e.fixture.v1", "variant":profile.stem,
  "source_revision":env::var("ASPIS_SOURCE_REVISION")?, "proof_bytes":proof.len(),
  "proof_sha256":sha(&proof),"public_bytes":public.len(),"public_sha256":sha(&public),
  "prover_seconds":prover_seconds,"prover_process_peak_rss_bytes":prover_process_peak_rss_bytes,
      "prover_rss_scope":"process high-water mark after preparation+prove, before native verify",
      "native_verifier_seconds":verifier_seconds,
  "query_count":22,"query_fibres":checked.queries.ordered(),"strict_native_accepted":true,
  "roundtrip":true,"release":!cfg!(debug_assertions),"fixture_entropy":"deterministic, insecure test fixture"});
    write_json(
        &dir.join(format!("{}.fixture.json", profile.stem)),
        &metadata,
    )?;
    println!("{}", metadata);
    Ok(())
}

fn markers(logs: &[String]) -> Vec<Value> {
    let mut result = Vec::new();
    let mut name = None;
    let mut previous = None;
    for log in logs {
        if let Some(label) = log.strip_prefix("Program log: r0:") {
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

fn measure(
    elf_path: &Path,
    fixture_dir: &Path,
    out: &Path,
    reject: bool,
    diagnostic: bool,
    profile: Profile,
) -> Result<()> {
    fs::create_dir_all(out)?;
    let elf = fs::read(elf_path)?;
    let mut proof = fs::read(fixture_dir.join(format!("{}.proof.bin", profile.stem)))?;
    let public = fs::read(fixture_dir.join(format!("{}.public.bin", profile.stem)))?;
    ensure!(public.len() == aspis_statement::pool_v1::POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES);
    let fixture: Value = serde_json::from_slice(&fs::read(
        fixture_dir.join(format!("{}.fixture.json", profile.stem)),
    )?)?;
    ensure!(fixture["variant"] == profile.stem);
    ensure!(fixture["query_count"] == 22);
    ensure!(fixture["proof_sha256"] == sha(&proof));
    ensure!(fixture["public_sha256"] == sha(&public));
    let original_proof_sha256 = sha(&proof);
    let mutation = if reject {
        let offset = aspis_statement::r0::OPENING_OFFSET + 5 * 6 + (29 + 58 + 1 + 6 + 256) * 32;
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
            "layout_source": "crates/aspis-core/src/r0/wire.rs"}),
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
    let public_key = Address::new_from_array([0x83; 32]);
    let data = vec![TAG];
    let ix = Instruction {
        program_id: program,
        accounts: vec![
            AccountMeta::new_readonly(proof_key, false),
            AccountMeta::new_readonly(public_key, false),
        ],
        data,
    };
    let budget = if diagnostic {
        200_000_000u64
    } else {
        LIMIT as u64
    };
    let label = if diagnostic {
        "DIAGNOSTIC: elevated CU only; no acceptance claim"
    } else {
        "ACCEPTANCE: 1,400,000 CU limit"
    };
    let mut first = None;
    for run in 1..=if reject || diagnostic { 1 } else { 5 } {
        let filename = if reject {
            format!("{}-reject-1.json", profile.stem)
        } else if diagnostic {
            format!("{}-diagnostic-{run}.json", profile.stem)
        } else {
            format!("{}-run-{run}.json", profile.stem)
        };
        ensure!(
            !out.join(&filename).exists(),
            "unchanged measurement rerun forbidden"
        );
        let start = Instant::now();
        let mut svm = LiteSVM::new();
        if diagnostic {
            let nesting = LiteSVM::mainnet_feature_set()
                .is_active(&agave_feature_set::raise_cpi_nesting_limit_to_8::ID);
            svm = svm.with_compute_budget(ComputeBudget {
                compute_unit_limit: budget,
                heap_size: 256 * 1024,
                ..ComputeBudget::new_with_defaults(nesting)
            });
        }
        svm.airdrop(&payer.pubkey(), 1_000_000_000)
            .map_err(|e| anyhow!("airdrop: {e:?}"))?;
        if let Err(error) = svm.add_program(program, &elf) {
            write_json(
                &out.join(&filename),
                &json!({
                    "label": label, "run": run, "load_error": format!("{error:?}"),
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
        svm.set_account(
            public_key,
            Account {
                lamports: 100_000_000,
                data: public.clone(),
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
        let execution = match svm.send_transaction(tx) {
            Ok(r) => (None, r),
            Err(r) => (Some(format!("{:?}", r.err)), r.meta),
        };
        let unchanged = svm.get_account(&proof_key).unwrap().data == account
            && svm.get_account(&public_key).unwrap().data == public;
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
        let heap_high_water_bytes = execution.1.logs.windows(2).find_map(|w| {
            if w[0] != "Program log: r0:heap-high-water" {
                return None;
            }
            let word = w[1]
                .strip_prefix("Program log: ")?
                .split(',')
                .next()?
                .trim()
                .strip_prefix("0x")?;
            u64::from_str_radix(word, 16).ok()
        });
        let record = json!({
            "schema": "aspis.r0-e2e-cu.run.v1", "label": label, "run": run,
            "variant": profile.stem, "query_count": 22, "proof_bytes": proof.len(),
            "proof_sha256": sha(&proof), "public_sha256": sha(&public), "elf_sha256": sha(&elf),
            "original_proof_sha256": original_proof_sha256, "mutation": mutation,
            "expected_rejection": reject,
            "elf_source_revision": env::var("ASPIS_ELF_SOURCE_REVISION").unwrap_or(env::var("ASPIS_SOURCE_REVISION")?),
            "source_revision": env::var("ASPIS_SOURCE_REVISION")?,
            "runtime": {"litesvm": "0.16.0", "agave": "4.2.1", "limit_cu": budget, "instruction_limit_cu": LIMIT, "diagnostic": diagnostic,
                "heap_bytes": 262144, "execution_wire": "legacy", "release_build": !cfg!(debug_assertions)},
            "txv1_bytes": txv1_bytes, "txv1_headroom_bytes": 4096 - txv1_bytes,
            "txv1_scope": "serialized signed verifier-only proposal; not executed as TxV1",
            "execution": {"error": execution.0, "cu": execution.1.compute_units_consumed,
                "logs": execution.1.logs},
            "identical_to_first_run": identical,
            "proof_and_public_accounts_unchanged": unchanged, "verifier_cu": verifier_cu,
            "verifier_completed": execution.0.is_none(), "phase_markers": phase_markers,
            "sbf_heap_high_water_bytes": heap_high_water_bytes,
            "wall_seconds": start.elapsed().as_secs_f64(),
            "excluded": ["pool CPI", "receipts", "settlement", "proof upload", "network execution"],
        });
        write_json(&out.join(&filename), &record)?;
        ensure!(
            unchanged && identical,
            "measurement disagreement: run {run}"
        );
        ensure!(
            heap_high_water_bytes.map_or(true, |n| n <= 262144),
            "STOP: runtime heap exceeds 256 KiB"
        );
        if diagnostic {
            ensure!(
                execution.0.is_none() && heap_high_water_bytes.is_some(),
                "diagnostic failed or heap measurement missing; do not rerun unchanged"
            );
        }
        // Runtime failures are preserved as failures, never converted into
        // completed verifier CU. Native corruption checks isolate each gate.
        println!(
            "run {run}: {label}; verifier CU {verifier_cu:?}; error {:?}",
            execution.0
        );
    }
    Ok(())
}

fn main() -> Result<()> {
    ensure!(!cfg!(debug_assertions), "release build required");
    let args: Vec<_> = env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("fixture") if (3..=4).contains(&args.len()) => fixture(Path::new(&args[2]), Profile::parse(args.get(3))?),
        Some("measure" | "reject" | "diagnostic") if (5..=6).contains(&args.len()) => measure(
            Path::new(&args[2]),
            Path::new(&args[3]),
            Path::new(&args[4]),
            args[1] == "reject",
            args[1] == "diagnostic",
            Profile::parse(args.get(5))?,
        ),
        _ => Err(anyhow!(
            "usage: r0-e2e-cu-probe fixture DIR [PROFILE] | measure|reject|diagnostic ELF FIXTURE_DIR RESULTS_DIR [PROFILE]"
        )),
    }
}
