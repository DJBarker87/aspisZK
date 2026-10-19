#![cfg(all(feature = "r0", feature = "insecure-spend-fixture"))]
use aspis_core::field::{WideExact, CM31, M31, QM31};
use aspis_core::state_only_prefix::r0::{self as wire, Error, Prefix};
use aspis_prover::{
    state_only_candidate_prefix::r0::*,
    v7_pair_forest_fixture::prepare_v7_pair_forest_transfer_fixture_v1, HOST_HASH,
};
use aspis_statement::pool_v1::{
    pair_forest_semantic_terminal::r0::Public,
    pair_forest_trace::compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
    pool_v1_tree_parent, PoolV1PairLiveSnapshotV1, PoolV1PaymentRelationContextV1,
    PoolV1PaymentRuntimeBindingV1,
};
use aspis_statement::state_only_verify::r0::verify_semantics;
use std::cell::Cell;
fn lift(n: u32) -> QM31 {
    QM31::from_cm31(CM31::from_m31(M31(n)))
}

// The semantic test commits message bytes only. R-D owns encoded-word trees
// and authentication. This adapter checks ordering/timing, not PCS security.
struct RecordingCommitments<'a> {
    phase: &'a Cell<u8>,
    d: &'a [QM31; 1024],
}
impl Commitments for RecordingCommitments<'_> {
    fn c1(&mut self, columns: [Column<'_>; 27]) -> Result<[u8; 32], Error> {
        assert_eq!(self.phase.get(), 0);
        self.phase.set(1);
        let mut data = vec![0xc1];
        for (lane, col) in columns.iter().enumerate() {
            match col {
                Column::Base(values) => {
                    assert!(lane < 26);
                    for x in *values {
                        data.extend_from_slice(&x.0.to_le_bytes());
                    }
                }
                Column::Extension(values) => {
                    assert_eq!(lane, 26);
                    assert_eq!(*values, self.d);
                    for x in *values {
                        let mut b = [0; 16];
                        x.write_le_bytes(&mut b);
                        data.extend_from_slice(&b);
                    }
                }
            }
        }
        Ok(HOST_HASH(&[&data]))
    }
    fn c2(&mut self, columns: [&[QM31; 1024]; 2]) -> Result<[u8; 32], Error> {
        assert_eq!(self.phase.get(), 2);
        self.phase.set(3);
        let mut data = vec![0xc2];
        for col in columns {
            for x in col {
                let mut b = [0; 16];
                x.write_le_bytes(&mut b);
                data.extend_from_slice(&b);
            }
        }
        Ok(HOST_HASH(&[&data]))
    }
}
fn fixture() -> aspis_prover::v7_pair_forest_fixture::PreparedV7PairForestTransferFixtureV1 {
    let mut empty = [[M31::ZERO; 8]; 21];
    empty[0] = pool_v1_tree_parent(&[M31::ZERO; 8], &[M31::ZERO; 8]);
    for i in 0..20 {
        empty[i + 1] = pool_v1_tree_parent(&empty[i], &empty[i]);
    }
    let snapshot = PoolV1PairLiveSnapshotV1 {
        pool: [1; 32],
        deployment_domain: [5; 32],
        sequence: 0,
        next_pair_index: 0,
        current_root: empty[20],
        frontier: core::array::from_fn(|i| empty[i]),
    };
    prepare_v7_pair_forest_transfer_fixture_v1([1; 32], [2; 32], [3; 32], 0, [5; 32], snapshot)
        .unwrap()
}

#[test]
fn honest_pair_forest_semantics_and_commitment_timing() {
    let f = fixture();
    let public = Public::Transfer(&f.public, &f.transition);
    let context = PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            pool: f.public.pool,
            deployment_domain: f.public.deployment_domain,
            anchor_sequence: f.public.anchor_sequence,
            anchor_root: f.public.anchor_root,
            asset_id: f.public.asset_id,
        },
        spent_nullifiers: &[],
    };
    let compiled = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
        &f.public,
        &f.witness,
        context,
        f.transition.live_snapshot,
    )
    .unwrap();
    let c1: [Vec<M31>; 26] = core::array::from_fn(|lane| {
        if lane < 16 {
            compiled.semantic_c1.c1[lane].clone()
        } else {
            (0..1024)
                .map(|r| M31((lane * 103 + r * 7 + 19) as u32))
                .collect()
        }
    });
    let d = core::array::from_fn(|row| QM31 {
        c0: CM31::new(M31(row as u32 + 3), M31(11)),
        c1: CM31::new(M31(17), M31(19)),
    });
    let g = core::array::from_fn(|row| lift(row as u32 + 5));
    let phase = Cell::new(0);
    let mut commitments = RecordingCommitments {
        phase: &phase,
        d: &d,
    };
    eprintln!(
        "heavy step: R0 pair-forest sumcheck generation (optimized; 28,644 oracle evaluations)"
    );
    let built=build_with_helper(public,&c1,&d,&g,|lambda,chi| {
        assert_eq!(phase.get(),1); phase.set(2);
        aspis_statement::pool_v1::pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1(
            &compiled.trace,0,lambda,chi).map_err(|_|Error::Public)
    },&mut commitments,HOST_HASH).unwrap();
    assert_eq!(phase.get(), 3);
    let checked = verify_semantics(public, &built.bytes, HOST_HASH).unwrap();
    assert_eq!(built.transcript.state(), checked.transcript.state());
    assert_eq!(built.alpha, checked.alpha);
    assert_eq!(built.state_before_z0, checked.state_before_z0);
    assert_eq!(built.roots, [checked.c1_root, checked.c2_root]);
    assert_eq!(built.challenges, checked.challenges);
    assert_eq!(built.z, checked.z);
    for point in &checked.claims {
        assert_ne!(point[28], WideExact::ZERO);
    }
    assert_eq!(built.bytes.len(), 12903);
    // Different field/public inputs are bound at C1 time.
    let mut changed_public = f.public;
    changed_public.asset_id = M31(78);
    assert!(verify_semantics(
        Public::Transfer(&changed_public, &f.transition),
        &built.bytes,
        HOST_HASH
    )
    .is_err());
    let mut altered = built.bytes.clone();
    altered[0] ^= 1;
    assert!(verify_semantics(public, &altered, HOST_HASH).is_err());
    let prefix = Prefix::parse(&built.bytes).unwrap();
    let row25 = 32
        + (0..25)
            .map(|r| prefix.record(r).unwrap().len())
            .sum::<usize>();
    for point in 0..3 {
        for lane in [0, 16, 26, 27, 28] {
            let mut changed = built.bytes.clone();
            let start = row25 + 5 + (point * 29 + lane) * 32;
            let x = WideExact::from_le_bytes(&changed[start..start + 32])
                .unwrap()
                .add(WideExact::ONE);
            changed[start..start + 32].copy_from_slice(&x.to_le_bytes());
            let result = verify_semantics(public, &changed, HOST_HASH);
            if let Ok(result) = result {
                assert_ne!(checked.transcript.state(), result.transcript.state());
            }
            // D intentionally has no terminal factor: its defect is R-D's gate,
            // while it MUST alter the beforeZ0 challenge and continuation state.
            if lane == 28 {
                let result = verify_semantics(public, &changed, HOST_HASH).unwrap();
                assert_ne!(result.z, checked.z);
            }
        }
    }
    // The actual PF terminal contains mu^2*(1-active)*H1, including E inputs.
    let mut ch = built.challenges;
    ch.theta = QM31::ZERO;
    ch.mu = lift(3);
    let alpha = [QM31::ONE; 10]; // row1023 is inactive and outside Poseidon.
    let mut claims = [[WideExact::ZERO; 29]; 3];
    claims[0][26] = WideExact::V;
    claims[0][28] = WideExact::ONE;
    assert_eq!(
        public.terminal(&claims, &alpha, &ch).unwrap(),
        WideExact::V.mul_qm31(lift(12))
    );
    // P1 beforeZ1 remains an independently bound message, not an equality
    // guard against a future row27 Y0 owned by the opening verifier.
    let mut changed = built.bytes.clone();
    let start = row25 + prefix.record(25).unwrap().len() + 5;
    let y = WideExact::from_le_bytes(&changed[start..start + 32])
        .unwrap()
        .add(WideExact::V);
    changed[start..start + 32].copy_from_slice(&y.to_le_bytes());
    assert!(verify_semantics(public, &changed, HOST_HASH).is_ok());
    if let Ok(directory) = std::env::var("R0_SEMANTIC_EVIDENCE_DIR") {
        let mut columns = Vec::new();
        for column in &built.columns {
            for value in column {
                let mut encoded = [0; 16];
                value.write_le_bytes(&mut encoded);
                columns.extend_from_slice(&encoded);
            }
        }
        std::fs::write(
            format!("{directory}/semantic-honest-pf-columns.bin"),
            columns,
        )
        .unwrap();
        std::fs::write(format!("{directory}/semantic-honest-pf.bin"), &built.bytes).unwrap();
        std::fs::write(
            format!("{directory}/semantic-honest-pf-public.bin"),
            public.public_bytes().unwrap(),
        )
        .unwrap();
        std::fs::write(
            format!("{directory}/semantic-honest-pf-state.bin"),
            built.transcript.state(),
        )
        .unwrap();
    }
}

#[test]
fn public_bytes_match_independent_p1_fixture() {
    use aspis_statement::pool_v1::{
        PoolV1PairLatePublicStatementV1, PoolV1PairVerifiedAfterstateV1,
        PoolV1PrivateTransferPublicV1,
    };
    let digest = |n| core::array::from_fn(|i| M31(n + i as u32));
    let public = PoolV1PrivateTransferPublicV1 {
        pool: [0; 32],
        deployment_domain: [0; 32],
        anchor_sequence: 0,
        anchor_root: digest(10),
        nullifier: digest(20),
        asset_id: M31(77),
        recipient_commitment: digest(30),
        change_commitment: digest(40),
    };
    let transition = PoolV1PairLatePublicStatementV1 {
        live_snapshot: PoolV1PairLiveSnapshotV1 {
            pool: [0; 32],
            deployment_domain: [0; 32],
            sequence: 9,
            next_pair_index: 9,
            current_root: [M31::ZERO; 8],
            frontier: core::array::from_fn(|i| digest(100 + i as u32 * 8)),
        },
        candidate_afterstate: PoolV1PairVerifiedAfterstateV1 {
            next_pair_index: 10,
            next_root: digest(50),
            next_frontier: core::array::from_fn(|i| digest(300 + i as u32 * 8)),
        },
    };
    assert_eq!(
        Public::Transfer(&public, &transition)
            .public_bytes()
            .unwrap(),
        include_bytes!("../../../results/r0-samplers-20261009/semantic-kat-public.bin")
    );
    assert_eq!(wire::C1_LANES[26], 28);
    assert_eq!(wire::C2_LANES, [26, 27]);
}

#[test]
fn equal_circle_points_reject_without_resampling() {
    thread_local! { static ROW: Cell<u8> = const { Cell::new(0) }; }
    fn forced(parts: &[&[u8]]) -> [u8; 32] {
        if parts.len() == 3 && parts[1].len() == 2 && parts[1][0] == 0 {
            ROW.with(|row| row.set(parts[1][1] - 0xa0));
        }
        if parts.len() == 2 && parts[1] == [1] && ROW.with(|row| row.get() >= 25) {
            // Non-CM31 parameter: both circle rows use the identical map,
            // so no distinct fallback can disguise equality.
            return [1; 32];
        }
        HOST_HASH(parts)
    }
    ROW.with(|row| row.set(0));
    let f = fixture();
    let proof = include_bytes!("../../../results/r0-samplers-20261009/semantic-honest-pf.bin");
    assert!(matches!(
        verify_semantics(Public::Transfer(&f.public, &f.transition), proof, forced),
        Err(Error::EqualCirclePoints)
    ));
    assert_eq!(ROW.with(Cell::get), 26);
}

#[test]
fn sparse_fixed_trace_prover_matches_independent_polynomials_claims_and_circle_values() {
    use aspis_core::r0::{domain::Point, encoder::eval_message};
    use aspis_core::state_only_prefix::r0::SemanticTranscript;
    let proof = include_bytes!("../../../results/r0-samplers-20261009/semantic-kat.bin");
    let public = include_bytes!("../../../results/r0-samplers-20261009/semantic-kat-public.bin");
    let prefix = Prefix::parse(proof).unwrap();
    let mut transcript = SemanticTranscript::new(HOST_HASH, public, prefix.c1_root).unwrap();
    wire::begin(&prefix, &mut transcript).unwrap();
    let mut output = Vec::new();
    let (alpha, terminal) = aspis_prover::state_only_hiding::r0::prove_sumcheck(
        &mut transcript,
        &mut output,
        lift(11264),
        |p| Ok(lift(7).add(p[9].mul(lift(3))).add(p[0].mul(lift(5)))),
    )
    .unwrap();
    let expected: Vec<u8> = (15..=24)
        .flat_map(|r| prefix.record(r).unwrap().iter().copied())
        .collect();
    assert_eq!(output, expected);
    let q = |limbs: [u32; 4]| QM31 {
        c0: CM31::new(M31(limbs[0]), M31(limbs[1])),
        c1: CM31::new(M31(limbs[2]), M31(limbs[3])),
    };
    let columns: [Vec<QM31>; 29] = core::array::from_fn(|lane| {
        (0..1024)
            .map(|r| match lane {
                0 => lift(7 + 3 * (r & 1) as u32 + 5 * (r >> 9) as u32),
                28 => q([11, 13, 17, 19])
                    .add(q([2, 3, 5, 7]).mul(lift((r & 1) as u32)))
                    .add(q([23, 29, 31, 37]).mul(lift((r >> 9) as u32))),
                _ => QM31::ZERO,
            })
            .collect()
    });
    let claims = point_claims(&columns, &alpha)
        .unwrap()
        .map(|row| row.map(WideExact::from_qm31));
    assert_eq!(claims, prefix.point_claims().unwrap());
    assert_eq!(WideExact::from_qm31(terminal), claims[0][0]);
    let z0 = transcript
        .challenge_reference_circle_point(25, prefix.record(25).unwrap())
        .unwrap();
    let expected = wire::decode_values::<29>(26, prefix.payload(26).unwrap()).unwrap();
    for lane in 0..29 {
        let message: &[QM31; 1024] = columns[lane].as_slice().try_into().unwrap();
        assert_eq!(
            WideExact::from_qm31(eval_message(message, Point { x: z0.x, y: z0.y })),
            expected[lane]
        );
    }
}
