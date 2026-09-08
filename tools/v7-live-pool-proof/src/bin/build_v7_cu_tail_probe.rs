use std::{env, fs, path::PathBuf, str::FromStr};

use anyhow::{ensure, Context, Result};
use aspis_verifier::v7_cu_tail_probe::{
    V7_CU_TAIL_COUNTER_TWENTY_TAG, V7_CU_TAIL_COUNTER_ZERO_TAG, V7_CU_TAIL_FRONTIER_199_TAG,
    V7_CU_TAIL_FRONTIER_203_TAG, V7_CU_TAIL_QM31_MAX_TAG, V7_CU_TAIL_QM31_MIN_TAG,
    V7_CU_TAIL_QUERY_ASCENDING_TAG, V7_CU_TAIL_QUERY_DESCENDING_TAG,
};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine as _};
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest as _, Sha256};
use solana_compute_budget_interface::ComputeBudgetInstruction;
use solana_keypair::read_keypair_file;
use solana_message::{legacy, VersionedMessage};
use solana_program::{hash::Hash, instruction::Instruction, pubkey::Pubkey};
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;

const DISPOSABLE_ACK: &str = "I_ACKNOWLEDGE_LOCAL_ONLY_V7_CU_TAIL_PROBE";

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Input {
    schema: String,
    disposable_acknowledgement: String,
    payer_keypair: String,
    recent_blockhash: String,
    min_context_slot: u64,
    request_id: u64,
    probe_program_id: String,
}

fn signed_request(
    payer: &solana_keypair::Keypair,
    program_id: Pubkey,
    blockhash: Hash,
    min_context_slot: u64,
    request_id: u64,
    name: &str,
    data: Vec<u8>,
) -> Result<Value> {
    let instruction = Instruction {
        program_id,
        accounts: Vec::new(),
        data,
    };
    let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
        &[
            ComputeBudgetInstruction::set_compute_unit_limit(1_400_000),
            instruction,
        ],
        Some(&payer.pubkey()),
        &blockhash,
    ));
    let transaction = VersionedTransaction::try_new(message, &[payer])
        .map_err(|error| anyhow::anyhow!("sign {name}: {error}"))?;
    let signature = transaction.signatures[0].to_string();
    let wire = bincode::serialize(&transaction)?;
    ensure!(wire.len() < 1_232, "{name} exceeds legacy packet envelope");
    let wire_base64 = BASE64.encode(&wire);
    Ok(json!({
        "name": name,
        "serializedTransactionBytes": wire.len(),
        "signedWireSha256": format!("{:x}", Sha256::digest(&wire)),
        "signature": signature,
        "simulationRequest": {
            "jsonrpc": "2.0", "id": request_id, "method": "simulateTransaction",
            "params": [wire_base64, {"encoding":"base64", "commitment":"confirmed",
                "sigVerify":true, "replaceRecentBlockhash":false,
                "minContextSlot":min_context_slot}]
        },
        "sendRequest": {
            "jsonrpc": "2.0", "id": request_id + 100_000, "method": "sendTransaction",
            "params": [wire_base64, {"encoding":"base64", "skipPreflight":true,
                "preflightCommitment":"confirmed", "minContextSlot":min_context_slot}]
        }
    }))
}

fn query_wire(tag: u8) -> Vec<u8> {
    let mut wire = Vec::with_capacity(65);
    wire.push(tag);
    for query in 0..16_u32 {
        wire.extend_from_slice(&query.to_le_bytes());
    }
    wire
}

fn main() -> Result<()> {
    let input_path = PathBuf::from(
        env::args_os()
            .nth(1)
            .context("usage: build-v7-cu-tail-probe <input.json>")?,
    );
    ensure!(env::args_os().nth(2).is_none(), "unexpected extra argument");
    let input: Input = serde_json::from_slice(&fs::read(input_path)?)?;
    ensure!(
        input.schema == "aspis.v7.cu-tail-probe-input.v1"
            && input.disposable_acknowledgement == DISPOSABLE_ACK
            && input.min_context_slot > 0,
        "wrong input schema, acknowledgement, or RPC identity"
    );
    let payer = read_keypair_file(&input.payer_keypair)
        .map_err(|error| anyhow::anyhow!("read disposable payer: {error}"))?;
    let program_id = Pubkey::from_str(&input.probe_program_id)?;
    let blockhash = Hash::from_str(&input.recent_blockhash)?;
    let cases = [
        ("qm31-minimum", vec![V7_CU_TAIL_QM31_MIN_TAG]),
        ("qm31-maximum-successful", vec![V7_CU_TAIL_QM31_MAX_TAG]),
        (
            "query-order-best",
            query_wire(V7_CU_TAIL_QUERY_ASCENDING_TAG),
        ),
        (
            "query-order-worst",
            query_wire(V7_CU_TAIL_QUERY_DESCENDING_TAG),
        ),
        ("counter-zero", vec![V7_CU_TAIL_COUNTER_ZERO_TAG]),
        ("counter-twenty", vec![V7_CU_TAIL_COUNTER_TWENTY_TAG]),
        ("frontier-199", vec![V7_CU_TAIL_FRONTIER_199_TAG]),
        ("frontier-203", vec![V7_CU_TAIL_FRONTIER_203_TAG]),
    ];
    let requests = cases
        .into_iter()
        .enumerate()
        .map(|(index, (name, data))| {
            signed_request(
                &payer,
                program_id,
                blockhash,
                input.min_context_slot,
                input.request_id + index as u64,
                name,
                data,
            )
        })
        .collect::<Result<Vec<_>>>()?;
    println!(
        "{}",
        json!({
            "schema": "aspis.v7.cu-tail-probe-signed-requests.v1",
            "localOnly": true,
            "probeProgramId": program_id.to_string(),
            "requests": requests,
        })
    );
    Ok(())
}
