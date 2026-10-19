//! Deterministic before/after trace for the J1 terminal-validation refactor.
//! Compare complete stdout bytes between pinned sources; this is finite
//! differential evidence, not a proof of refinement or verifier acceptance.
use aspis_core::field::{M31, P};
use aspis_statement::pool_v1::{
    pair_forest_accounts::pool_v1_pair_forest_output_lane_v1,
    pair_terminal::{encode_pool_v1_pair_verified_afterstate_v1, PoolV1PairVerifiedAfterstateV1},
    pair_tree_profile::{
        encode_pool_v1_pair_late_public_statement_v1, encode_pool_v1_pair_live_snapshot_v1,
        PoolV1PairLatePublicStatementV1, PoolV1PairLiveSnapshotV1,
        POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES, POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,
    },
    POOL_V1_PAIR_CAPACITY, POOL_V1_PAIR_TREE_DEPTH,
};
use std::io::{self, BufWriter, Write};

fn emit(
    out: &mut impl Write,
    id: usize,
    snapshot: PoolV1PairLiveSnapshotV1,
    afterstate: PoolV1PairVerifiedAfterstateV1,
    nullifier: [M31; 8],
    lengths: bool,
) -> io::Result<()> {
    writeln!(out, "case {id}")?;
    writeln!(
        out,
        "lane {:?}",
        pool_v1_pair_forest_output_lane_v1(&nullifier)
    )?;
    writeln!(
        out,
        "after {:?}",
        encode_pool_v1_pair_verified_afterstate_v1(&afterstate)
    )?;
    let late = PoolV1PairLatePublicStatementV1 {
        live_snapshot: snapshot,
        candidate_afterstate: afterstate,
    };
    let extras: &[isize] = if lengths { &[-1, 0, 1] } else { &[0] };
    for extra in extras {
        let mut bytes = vec![0xa5; (POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES as isize + extra) as usize];
        let result = encode_pool_v1_pair_live_snapshot_v1(&snapshot, &mut bytes);
        writeln!(out, "snapshot {extra} {result:?} {bytes:?}")?;
        let mut bytes =
            vec![0xa5; (POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES as isize + extra) as usize];
        let result = encode_pool_v1_pair_late_public_statement_v1(&late, &mut bytes);
        writeln!(out, "late {extra} {result:?} {bytes:?}")?;
    }
    Ok(())
}

fn main() -> io::Result<()> {
    let mut out = BufWriter::new(io::stdout().lock());
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: [1; 32],
        deployment_domain: [2; 32],
        sequence: 7,
        next_pair_index: 7,
        current_root: [M31(0); 8],
        frontier: [[M31(0); 8]; POOL_V1_PAIR_TREE_DEPTH],
    };
    let afterstate = PoolV1PairVerifiedAfterstateV1 {
        next_pair_index: 8,
        next_root: [M31(0); 8],
        next_frontier: [[M31(0); 8]; POOL_V1_PAIR_TREE_DEPTH],
    };
    let mut id = 0;
    emit(&mut out, id, snapshot, afterstate, [M31(0); 8], true)?;
    id += 1;
    // Every root/frontier coordinate, including each noncanonical boundary.
    for position in 0..8 * (POOL_V1_PAIR_TREE_DEPTH + 1) {
        for raw in [0, 1, P - 1, P, P + 1, u32::MAX] {
            let mut s = snapshot;
            let mut a = afterstate;
            let mut n = [M31(0); 8];
            n[position % 8] = M31(raw);
            if position < 8 {
                s.current_root[position] = M31(raw);
                a.next_root[position] = M31(raw);
            } else {
                s.frontier[position / 8 - 1][position % 8] = M31(raw);
                a.next_frontier[position / 8 - 1][position % 8] = M31(raw);
            }
            emit(&mut out, id, s, a, n, false)?;
            id += 1;
        }
    }
    // Combined invalid inputs exercise error priority and unchanged buffers.
    for index in [
        0,
        1,
        7,
        POOL_V1_PAIR_CAPACITY - 1,
        POOL_V1_PAIR_CAPACITY,
        POOL_V1_PAIR_CAPACITY + 1,
        u64::MAX,
    ] {
        for flags in 0..32 {
            let mut s = snapshot;
            let mut a = afterstate;
            s.sequence = index;
            s.next_pair_index = index;
            a.next_pair_index = index.wrapping_add(1);
            if flags & 1 != 0 {
                s.pool = [0; 32];
            }
            if flags & 2 != 0 {
                s.deployment_domain = [0; 32];
            }
            if flags & 4 != 0 {
                s.sequence = index.wrapping_add(2);
            }
            if flags & 8 != 0 {
                s.current_root[0] = M31(P);
            }
            if flags & 16 != 0 {
                a.next_frontier[POOL_V1_PAIR_TREE_DEPTH - 1][7] = M31(P);
            }
            emit(&mut out, id, s, a, [M31(0); 8], true)?;
            id += 1;
        }
    }
    writeln!(out, "complete {id}")?;
    out.flush()
}
