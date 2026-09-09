//! Fixed-seed synthetic note, with membership exported from authenticated live state.
use aspis_core::field::M31;
use aspis_statement::{derive_owner_key, pool_v1::*, pool_v1::pair_trace::PoolV1PairInputNoteWitnessV1};
fn dig(s: u32) -> [M31; 8] { std::array::from_fn(|i| M31(s + 17 * i as u32 + 1)) }
pub fn load() -> (PoolV1PrivateTransferPublicV1, PoolV1PairForestPrivateTransferWitnessV1, PoolV1PairLiveSnapshotV1) {
    let dir = std::env::var("ASPIS_V8_LIVE_CONTEXT").unwrap();
    let bytes = std::fs::read(format!("{dir}/statement.bin")).unwrap();
    let s = decode_pool_v1_pair_forest_terminal_statement_v1(&bytes).unwrap();
    validate_pool_v1_pair_forest_terminal_statement_v1(&s).unwrap();
    let p = match s { PoolV1PairForestTerminalStatementV1::PrivateTransfer { public, .. } => public, _ => panic!("transfer only") };
    let m = std::fs::read(format!("{dir}/membership.bin")).unwrap();
    assert_eq!(m.len(), 20 * 32 + 3 * 32 + 3);
    let digest = |at: usize| -> [M31; 8] {
        std::array::from_fn(|i| { let n = u32::from_le_bytes(m[at+4*i..at+4*i+4].try_into().unwrap()); assert!(n < aspis_core::field::P); M31(n) })
    };
    let key = dig(10); let salt = dig(100);
    let leaf = pool_v1_note_commitment(&derive_owner_key(&key), 1000, p.asset_id, &salt);
    let w = PoolV1PairForestPrivateTransferWitnessV1 {
        input: PoolV1PairForestInputNoteWitnessV1 {
            pair: PoolV1PairInputNoteWitnessV1 {
                nullifier_key: key, salt, value: 1000,
                pair_leaf: PoolV1PairLeafWitnessV1::single_output(leaf).unwrap(), selected_second: false,
                membership: PoolV1MembershipWitnessV1 { siblings: std::array::from_fn(|i| digest(i*32)), index: 0 },
            },
            super_root_siblings: std::array::from_fn(|i| digest(640+i*32)),
            super_root_directions: std::array::from_fn(|i| { assert!(m[736+i] <= 1); m[736+i] == 1 }),
        },
        recipient: PoolV1OutputNoteWitnessV1 { owner_key: derive_owner_key(&dig(300)), salt: dig(400), value: 600 },
        change: PoolV1OutputNoteWitnessV1 { owner_key: derive_owner_key(&dig(500)), salt: dig(600), value: 400 },
    };
    (p, w, s.common().lane_transition.live_snapshot)
}
