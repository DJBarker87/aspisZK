use std::{
    env, fs,
    str::FromStr,
    sync::atomic::{AtomicUsize, Ordering},
};

use anyhow::{bail, ensure, Context, Result};
use aspis_core::v7_fixed_canonical_audit::V7_CANONICAL_BODY_WITHOUT_FRONTIERS;
use aspis_core::v7_onefold::V7_COMPACT_DIGEST_BYTES;
use aspis_prover::HOST_HASH;
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_forest_terminal_statement_v1,
    v7_pool_pair_forest_tag73_statement_digest_v1, PoolV1PairForestTerminalStatementV1,
    V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
};
use solana_program::pubkey::Pubkey;

static HASH_CALLS: AtomicUsize = AtomicUsize::new(0);
static ONE_SLICE_33_BYTE_HASH_CALLS: AtomicUsize = AtomicUsize::new(0);
static CAUSAL_BIND_HASH_CALLS: AtomicUsize = AtomicUsize::new(0);

fn diagnostic_hash(values: &[&[u8]]) -> [u8; 32] {
    HASH_CALLS.fetch_add(1, Ordering::Relaxed);
    if values.len() == 1 && values[0].len() == 33 {
        ONE_SLICE_33_BYTE_HASH_CALLS.fetch_add(1, Ordering::Relaxed);
    }
    if values.len() == 4
        && values[0].len() == 32
        && values[1].len() == 2
        && values[2].len() == 2
        && values[3].len() == 384
    {
        CAUSAL_BIND_HASH_CALLS.fetch_add(1, Ordering::Relaxed);
    }
    HOST_HASH(values)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transcript_and_causal_bind_hash_shapes_are_counted_exactly() {
        let squeeze = [0u8; 33];
        diagnostic_hash(&[&squeeze]);
        let state = [0u8; 32];
        let frame = [0u8; 2];
        let header = [0u8; 2];
        let raw = [0u8; 384];
        diagnostic_hash(&[&state, &frame, &header, &raw]);
        assert_eq!(HASH_CALLS.load(Ordering::Relaxed), 2);
        assert_eq!(ONE_SLICE_33_BYTE_HASH_CALLS.load(Ordering::Relaxed), 1);
        assert_eq!(CAUSAL_BIND_HASH_CALLS.load(Ordering::Relaxed), 1);
    }
}

fn main() -> Result<()> {
    let mut args = env::args().skip(1);
    let statement_path = args.next().context("missing ASF8 path")?;
    let proof_path = args.next().context("missing proof-body path")?;
    let verifier = Pubkey::from_str(&args.next().context("missing verifier program id")?)
        .context("invalid verifier program id")?;
    let attempt = Pubkey::from_str(&args.next().context("missing proof-account attempt id")?)
        .context("invalid proof-account attempt id")?;
    ensure!(args.next().is_none(), "unexpected trailing argument");

    let statement_bytes: [u8; 1880] = fs::read(statement_path)
        .context("read ASF8")?
        .try_into()
        .map_err(|bytes: Vec<u8>| {
            anyhow::anyhow!("ASF8 has {} bytes, expected 1880", bytes.len())
        })?;
    let statement = decode_pool_v1_pair_forest_terminal_statement_v1(&statement_bytes)
        .map_err(|error| anyhow::anyhow!("decode ASF8: {error:?}"))?;
    let proof = fs::read(proof_path).context("read proof body")?;
    let frontier_bytes = proof
        .len()
        .checked_sub(V7_CANONICAL_BODY_WITHOUT_FRONTIERS)
        .context("proof shorter than canonical fixed body")?;
    let bytes_per_paired_node = 2 * V7_COMPACT_DIGEST_BYTES;
    ensure!(
        frontier_bytes % bytes_per_paired_node == 0,
        "proof length does not encode two exact frontiers"
    );
    let frontier_nodes = frontier_bytes / bytes_per_paired_node;
    let statement_digest =
        v7_pool_pair_forest_tag73_statement_digest_v1(&statement_bytes, HOST_HASH);
    let transition = &statement.common().lane_transition;
    let verified = match &statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { ref public, .. } => {
            aspis_verifier::v7_verifier::verify_v7_pool_pair_forest_private_transfer_canonical_with_statement_digest(
                diagnostic_hash,
                &proof,
                frontier_nodes,
                &verifier,
                V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
                &attempt,
                public,
                transition,
                statement_digest,
                true,
            )
        }
        PoolV1PairForestTerminalStatementV1::Withdrawal { ref public, .. } => {
            aspis_verifier::v7_verifier::verify_v7_pool_pair_forest_withdrawal_canonical_with_statement_digest(
                diagnostic_hash,
                &proof,
                frontier_nodes,
                &verifier,
                V7_POOL_PAIR_FOREST_TAG73_RELEASE_BINDING,
                &attempt,
                public,
                transition,
                statement_digest,
                true,
            )
        }
    };
    let verified = match verified {
        Ok(value) => value,
        Err(error) => bail!("proof verification failed: {error:?}"),
    };
    let squeeze_sha_calls = ONE_SLICE_33_BYTE_HASH_CALLS.load(Ordering::Relaxed);
    ensure!(
        squeeze_sha_calls % 2 == 0,
        "odd number of transcript squeeze SHA calls"
    );
    let causal_bind_hash_calls = CAUSAL_BIND_HASH_CALLS.load(Ordering::Relaxed);
    ensure!(
        causal_bind_hash_calls == 2,
        "Tag-73 profile must contain exactly two causal challenge binds"
    );
    println!(
        "{}",
        serde_json::json!({
            "schema":"aspis.v7.live-proof-inspection.v2",
            "proofBytes":proof.len(),
            "frontierNodes":verified.transcript.frontier_nodes,
            "compactCounter":verified.transcript.compact_counter,
            "hashDiagnostics":{
                "allHashCalls":HASH_CALLS.load(Ordering::Relaxed),
                "oneSlice33ByteHashCalls":squeeze_sha_calls,
                "transcriptSqueezeBlocks":squeeze_sha_calls / 2,
                "causalBindHashCalls":causal_bind_hash_calls,
                "causalBindInputBytes":420,
                "causalBindSlices":4
            }
        })
    );
    Ok(())
}
