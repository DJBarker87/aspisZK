use std::{env, fs, os::unix::fs::PermissionsExt, path::PathBuf, str::FromStr};

use anyhow::{ensure, Context, Result};
use aspis_pool_wallet_v1::registry_transaction_builder::{
    build_activate_registry_entry_instruction_v2, build_freeze_registry_instruction_v2,
    build_initialize_registry_instruction_v2,
    build_schedule_pair_forest_tag73_profile_instruction_v2, RegistryEntryKeyV1,
    RegistryGovernanceRouteV1,
};
use aspis_registry::{pool_v1_verifier_entry_v2_address, pool_v1_verifier_registry_v2_address};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine as _};
use serde::Deserialize;
use serde_json::json;
use sha2::{Digest as _, Sha256};
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_keypair::read_keypair_file;
use solana_message::{legacy, VersionedMessage};
use solana_program::{hash::Hash, pubkey::Pubkey};
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;

const DEVNET_GENESIS_HASH: &str = "EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG";

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Input {
    schema: String,
    action: String,
    genesis_hash: String,
    registry_program: String,
    pool: String,
    verifier_program: String,
    registry_executable_sha256: String,
    verifier_executable_sha256: String,
    policy_binding_hex: String,
    payer_keypair: String,
    authority_keypair: String,
    recent_blockhash: String,
    min_context_slot: u64,
    request_id: u64,
    #[serde(default)]
    activation_slot: Option<u64>,
}

fn hex32(value: &str, label: &str) -> Result<[u8; 32]> {
    ensure!(value.len() == 64, "{label} has wrong length");
    let bytes = hex::decode(value).with_context(|| format!("decode {label}"))?;
    bytes
        .try_into()
        .map_err(|_| anyhow::anyhow!("{label} has wrong decoded length"))
}

fn secure_keypair(path: &str, label: &str) -> Result<solana_keypair::Keypair> {
    let metadata = fs::symlink_metadata(path).with_context(|| format!("stat {label}"))?;
    ensure!(
        metadata.file_type().is_file()
            && !metadata.file_type().is_symlink()
            && metadata.permissions().mode() & 0o077 == 0,
        "{label} must be a non-symlink regular file with no group/other permissions"
    );
    read_keypair_file(path).map_err(|error| anyhow::anyhow!("read {label}: {error}"))
}

fn main() -> Result<()> {
    let input_path = PathBuf::from(
        env::args_os()
            .nth(1)
            .context("usage: build-public-devnet-registry <input.json>")?,
    );
    ensure!(env::args_os().nth(2).is_none(), "unexpected extra argument");
    let input: Input = serde_json::from_slice(&fs::read(&input_path)?)?;
    ensure!(
        input.schema == "aspis.v7.public-devnet-registry-input.v1"
            && input.genesis_hash == DEVNET_GENESIS_HASH
            && input.min_context_slot > 0
            && input.request_id > 0,
        "wrong schema, cluster, or RPC identity"
    );

    let registry_program = Pubkey::from_str(&input.registry_program)?;
    let pool = Pubkey::from_str(&input.pool)?;
    let verifier_program = Pubkey::from_str(&input.verifier_program)?;
    let payer = secure_keypair(&input.payer_keypair, "payer keypair")?;
    let authority = secure_keypair(&input.authority_keypair, "authority keypair")?;
    ensure!(
        payer.pubkey() != authority.pubkey(),
        "registry payer and governance authority must be distinct"
    );
    let route = RegistryGovernanceRouteV1 {
        authority: authority.pubkey(),
        payer: payer.pubkey(),
    };
    let entry_key = RegistryEntryKeyV1::pair_forest_tag73_v1();
    let instruction = match input.action.as_str() {
        "initialize" => {
            ensure!(
                input.activation_slot.is_none(),
                "unexpected activation slot"
            );
            build_initialize_registry_instruction_v2(
                registry_program,
                pool,
                hex32(&input.policy_binding_hex, "policy binding")?,
                1,
                hex32(
                    &input.registry_executable_sha256,
                    "Registry executable SHA-256",
                )?,
                route,
            )
        }
        "schedule" => build_schedule_pair_forest_tag73_profile_instruction_v2(
            registry_program,
            pool,
            0,
            verifier_program,
            hex32(
                &input.verifier_executable_sha256,
                "verifier executable SHA-256",
            )?,
            input
                .activation_slot
                .context("schedule requires activation slot")?,
            route,
        ),
        "activate" => {
            ensure!(
                input.activation_slot.is_none(),
                "unexpected activation slot"
            );
            build_activate_registry_entry_instruction_v2(
                registry_program,
                pool,
                1,
                entry_key,
                authority.pubkey(),
            )
        }
        "freeze" => {
            ensure!(
                input.activation_slot.is_none(),
                "unexpected activation slot"
            );
            build_freeze_registry_instruction_v2(registry_program, pool, 2, authority.pubkey())
        }
        _ => anyhow::bail!("unsupported Registry action"),
    }
    .map_err(|error| anyhow::anyhow!("build Registry instruction: {error:?}"))?;

    let blockhash = Hash::from_str(&input.recent_blockhash).context("invalid blockhash")?;
    let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(1_400_000),
            instruction,
        ],
        Some(&payer.pubkey()),
        &blockhash,
    ));
    let transaction = VersionedTransaction::try_new(message, &[&payer, &authority])
        .map_err(|error| anyhow::anyhow!("sign Registry transaction: {error}"))?;
    let wire = bincode::serialize(&transaction)?;
    ensure!(
        wire.len() < 1_232,
        "Registry transaction exceeds legacy envelope"
    );
    let wire_base64 = BASE64.encode(&wire);
    let registry = pool_v1_verifier_registry_v2_address(&registry_program, &pool).0;
    let entry = pool_v1_verifier_entry_v2_address(
        &registry_program,
        &pool,
        &entry_key.profile_binding,
        &entry_key.release_binding,
    )
    .0;

    println!(
        "{}",
        json!({
            "schema":"aspis.v7.public-devnet-registry-signed-request.v1",
            "cluster":"devnet",
            "genesisHash":DEVNET_GENESIS_HASH,
            "action":input.action,
            "registryProgram":registry_program.to_string(),
            "registryAccount":registry.to_string(),
            "entryAccount":entry.to_string(),
            "pool":pool.to_string(),
            "verifierProgram":verifier_program.to_string(),
            "payer":payer.pubkey().to_string(),
            "authority":authority.pubkey().to_string(),
            "serializedTransactionBytes":wire.len(),
            "signedWireSha256":format!("{:x}", Sha256::digest(&wire)),
            "signature":transaction.signatures[0].to_string(),
            "simulationRequest":{
                "jsonrpc":"2.0","id":input.request_id,"method":"simulateTransaction",
                "params":[wire_base64,{"encoding":"base64","commitment":"confirmed",
                    "sigVerify":true,"replaceRecentBlockhash":false,
                    "minContextSlot":input.min_context_slot}]
            },
            "sendRequest":{
                "jsonrpc":"2.0","id":input.request_id+100_000,"method":"sendTransaction",
                "params":[wire_base64,{"encoding":"base64","skipPreflight":true,
                    "preflightCommitment":"confirmed","maxRetries":0,
                    "minContextSlot":input.min_context_slot}]
            }
        })
    );
    Ok(())
}
