use aspis_core::{
    circle::secure_ood_circle_point_from_parameter,
    field::{CM31, M31, P, QM31},
    state_only_prefix::{
        StateOnlyPrefixScheduleResult, StateOnlyTranscriptScheduleResult,
        STATE_ONLY_MAX_QUERY_COUNT,
    },
    statement_sumcheck::PaymentConstraintChallenges,
    v8_a100::V8_A100_MAX_FRONTIER_FIXTURE,
};
use aspis_prover::state_only_hiding_rank::{
    probe_v8_a100_pool_pair_forest_per_c1_image_containment,
    probe_v8_a100_pool_pair_per_c1_image_containment,
    probe_v8_a100_pool_v1_pair_forest_root_message_hiding_rank,
    probe_v8_a100_pool_v1_pair_root_message_hiding_rank, StateOnlyHidingRankGateError,
};

fn pseudorandom_m31(seed: u64) -> M31 {
    let mut value = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^= value >> 31;
    M31((value % u64::from(P)) as u32)
}

fn qm31(seed: u32) -> QM31 {
    let seed = u64::from(seed) * 4;
    QM31 {
        c0: CM31::new(pseudorandom_m31(seed), pseudorandom_m31(seed + 1)),
        c1: CM31::new(pseudorandom_m31(seed + 2), pseudorandom_m31(seed + 3)),
    }
}

fn conjugate_pair_schedule() -> StateOnlyTranscriptScheduleResult {
    let mut queries = [0u32; STATE_ONLY_MAX_QUERY_COUNT];
    queries[..22].copy_from_slice(&V8_A100_MAX_FRONTIER_FIXTURE);

    let parameter0 = qm31(101);
    let parameter1 = parameter0.pow(u64::from(P));
    let point0 = secure_ood_circle_point_from_parameter(parameter0).unwrap();
    let point1 = secure_ood_circle_point_from_parameter(parameter1).unwrap();
    assert_ne!(point0, point1);

    StateOnlyTranscriptScheduleResult {
        prefix: StateOnlyPrefixScheduleResult {
            lambda: qm31(2),
            chi: qm31(3),
            batching: PaymentConstraintChallenges {
                theta: qm31(5),
                zerocheck_point: core::array::from_fn(|index| qm31(7 + index as u32)),
                mu: qm31(19),
            },
            initial_mask_claim: qm31(23),
            eta: qm31(29),
            z: core::array::from_fn(|index| qm31(31 + index as u32)),
            masked_terminal_claim: qm31(43),
            gamma: qm31(47),
            point_scale: qm31(53),
            state_after_gamma: [0u8; 32],
        },
        circle_ood_points: [point0, point1],
        line_ood_points: [[QM31::ZERO; 2]; 3],
        mu: [[QM31::ZERO; 2]; 4],
        alpha: [qm31(59), qm31(61), qm31(67), qm31(71)],
        state_before_grinding: [0u8; 32],
        queries,
        query_count: 22,
        state_after_queries: [0u8; 32],
    }
}

/// Expensive host rank replay.  The exact source gate rejects the legal
/// distinct secure Frobenius pair at the first C1 raw block: it demands the
/// stronger ambient rank 108 although the two OOD coordinates contribute a
/// four-dimensional graph, reducing the attainable rank to 104.
#[test]
#[ignore = "optimized exact host rank replay; run explicitly"]
fn v8_pair_ambient_rank_rejects_legal_frobenius_pair() {
    assert_eq!(
        probe_v8_a100_pool_v1_pair_root_message_hiding_rank(&conjugate_pair_schedule()),
        Err(StateOnlyHidingRankGateError::RawC1Rank {
            column: 0,
            got: 104,
            want: 108,
        })
    );
}

/// The pair-forest registry hits the same exact obstruction.  The failure is
/// independent of the statement layout because it occurs in the common C1
/// two-OOD raw block before the later mask/source containment calculation.
#[test]
#[ignore = "optimized exact host rank replay; run explicitly"]
fn v8_pair_forest_ambient_rank_rejects_legal_frobenius_pair() {
    assert_eq!(
        probe_v8_a100_pool_v1_pair_forest_root_message_hiding_rank(&conjugate_pair_schedule()),
        Err(StateOnlyHidingRankGateError::RawC1Rank {
            column: 0,
            got: 104,
            want: 108,
        })
    );
}

#[test]
fn v8_conjugate_pair_per_c1_physical_image_is_contained() {
    for report in [
        probe_v8_a100_pool_pair_per_c1_image_containment(&conjugate_pair_schedule()).unwrap(),
        probe_v8_a100_pool_pair_forest_per_c1_image_containment(&conjugate_pair_schedule())
            .unwrap(),
    ] {
        println!("{report:?}");
        assert_eq!(report.query_count, 22);
        assert_eq!(report.ambient_raw_m31, 108);
        assert_eq!(report.mask_rank_m31, [104; 16]);
        assert_eq!(report.physical_superset_generators, [1022; 16]);
        assert!(report.physical_superset_contained);
    }
}
