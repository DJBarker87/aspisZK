//! Deterministic full-result trace for the J1 decoder extraction refactor.
//! Invoke with the retained public ASF8 fixture path, never a private key.
use aspis_statement::pool_v1::{
    decode_pool_v1_pair_forest_terminal_statement_v1,
    decode_pool_v1_pair_late_public_statement_v1, decode_pool_v1_pair_live_snapshot_v1,
    decode_pool_v1_pair_verified_afterstate_v1,
    encode_pool_v1_pair_forest_terminal_statement_v1,
    encode_pool_v1_pair_late_public_statement_v1, encode_pool_v1_pair_live_snapshot_v1,
    encode_pool_v1_pair_verified_afterstate_v1, PoolV1PairForestTerminalStatementV1,
    PoolV1PrivateTransferPublicV1, PoolV1WithdrawalPublicV1,
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES, POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,
};
use std::io::{self, BufWriter, Write};

fn exercise(
    out: &mut impl Write,
    label: &str,
    baseline: &[u8],
    decode: fn(&[u8]) -> String,
) -> io::Result<usize> {
    let mut count = 0;
    writeln!(out, "{label} baseline {}", decode(baseline))?;
    count += 1;
    // All length checks, including one overlength input.
    for len in 0..=baseline.len() + 1 {
        let mut bytes = baseline.to_vec();
        bytes.resize(len, 0);
        writeln!(out, "{label} length {len} {}", decode(&bytes))?;
        count += 1;
    }
    // Every framing, metadata, canonical limb and reserved-byte position.
    for i in 0..baseline.len() {
        for value in [0, 0xff] {
            let mut bytes = baseline.to_vec();
            bytes[i] = value;
            writeln!(out, "{label} byte {i} {value} {}", decode(&bytes))?;
            count += 1;
        }
    }
    // Simultaneous corruptions retain evidence of first-error priority.
    for i in (0..baseline.len()).step_by(17) {
        let mut bytes = baseline.to_vec();
        bytes[0] ^= 0xff;
        bytes[i] ^= 0xff;
        writeln!(out, "{label} pair {i} {}", decode(&bytes))?;
        count += 1;
    }
    Ok(count)
}

fn main() -> io::Result<()> {
    let path = std::env::args().nth(1).expect("public ASF8 fixture path");
    let fixture = std::fs::read(path)?;
    let statement = decode_pool_v1_pair_forest_terminal_statement_v1(&fixture)
        .expect("valid public ASF8 fixture");
    let common = *statement.common();
    let transfer = match statement {
        PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => public,
        PoolV1PairForestTerminalStatementV1::Withdrawal { public, .. } => {
            PoolV1PrivateTransferPublicV1 {
                pool: public.pool,
                deployment_domain: public.deployment_domain,
                anchor_sequence: public.anchor_sequence,
                anchor_root: public.anchor_root,
                nullifier: public.nullifier,
                asset_id: public.asset_id,
                recipient_commitment: public.change_commitment,
                change_commitment: public.change_commitment,
            }
        }
    };
    let withdrawal = PoolV1WithdrawalPublicV1 {
        pool: transfer.pool,
        deployment_domain: transfer.deployment_domain,
        anchor_sequence: transfer.anchor_sequence,
        anchor_root: transfer.anchor_root,
        nullifier: transfer.nullifier,
        asset_id: transfer.asset_id,
        amount: 1,
        destination_token_account: [3; 32],
        change_commitment: transfer.change_commitment,
    };
    let mut out = BufWriter::new(io::stdout().lock());
    let mut count = 0;
    for (label, input) in [
        ("transfer", PoolV1PairForestTerminalStatementV1::PrivateTransfer { common, public: transfer }),
        ("withdrawal", PoolV1PairForestTerminalStatementV1::Withdrawal { common, public: withdrawal }),
    ] {
        let bytes = encode_pool_v1_pair_forest_terminal_statement_v1(&input).unwrap();
        count += exercise(&mut out, label, &bytes, |b| {
            format!("{:?}", decode_pool_v1_pair_forest_terminal_statement_v1(b))
        })?;
    }
    let mut snapshot = vec![0; POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES];
    encode_pool_v1_pair_live_snapshot_v1(&common.lane_transition.live_snapshot, &mut snapshot).unwrap();
    count += exercise(&mut out, "snapshot", &snapshot, |b| {
        format!("{:?}", decode_pool_v1_pair_live_snapshot_v1(b))
    })?;
    let after = encode_pool_v1_pair_verified_afterstate_v1(&common.lane_transition.candidate_afterstate).unwrap();
    count += exercise(&mut out, "afterstate", &after, |b| {
        format!("{:?}", decode_pool_v1_pair_verified_afterstate_v1(b))
    })?;
    let mut late = vec![0; POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES];
    encode_pool_v1_pair_late_public_statement_v1(&common.lane_transition, &mut late).unwrap();
    count += exercise(&mut out, "late", &late, |b| {
        format!("{:?}", decode_pool_v1_pair_late_public_statement_v1(b))
    })?;
    writeln!(out, "complete {count}")?;
    out.flush()
}
