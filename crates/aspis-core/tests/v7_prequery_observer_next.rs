#![cfg(feature = "aeneas-observer")]
//! These are differential/shape tests, not substitutes for an Aeneas proof.
use aspis_core::field::{CM31, M31, QM31};
use aspis_core::sumcheck::WeightAccumulator;
use aspis_core::v6_transcript::{
    prequery_dot_256, snapshot_query_batch_prechallenge, V6QueryBatchPrechallengeView,
};

fn q(x: u32) -> QM31 {
    QM31::from_cm31(CM31::from_m31(M31(x % 2_147_483_647)))
}
fn ext(x: u32) -> QM31 {
    QM31 {
        c0: CM31::new(M31(x % 2_147_483_647), M31((x + 1) % 2_147_483_647)),
        c1: CM31::new(M31((x + 2) % 2_147_483_647), M31((x + 3) % 2_147_483_647)),
    }
}
fn coefficients(seed: u32) -> [QM31; 256] {
    core::array::from_fn(|i| ext(seed + 37 * i as u32))
}
fn direct(weights: &WeightAccumulator, values: &[QM31; 256]) -> QM31 {
    values.iter().enumerate().fold(QM31::ZERO, |sum, (i, value)| {
        sum.add(value.mul(weights.weight_at(i as u32)))
    })
}
fn check(weights: &WeightAccumulator, seed: u32) {
    let values = coefficients(seed);
    let before = values;
    assert_eq!(prequery_dot_256(weights, &values), direct(weights, &values));
    assert_eq!(prequery_dot_256(weights, &values), weights.dot(&values[..]));
    assert_eq!(values, before);
}

#[test]
fn every_coefficient_including_255_is_observed() {
    let mut weights = WeightAccumulator::empty(8);
    weights.add_geometric(QM31::ONE, QM31::ONE);
    for position in 0..256 {
        let mut values = [QM31::ZERO; 256];
        values[position] = QM31::ONE;
        assert_eq!(prequery_dot_256(&weights, &values), QM31::ONE);
    }
}

#[test]
fn empty_and_dense_covectors() {
    check(&WeightAccumulator::empty(8), 0);
    let mut weights = WeightAccumulator::empty(8);
    weights.add_dense((0..256).map(|i| ext(i * 11)).collect()).unwrap();
    check(&weights, 31);
}

#[test]
fn full_width_structured_components_and_mixture() {
    let mut weights = WeightAccumulator::empty(8);
    weights.add_geometric(ext(3), ext(5));
    check(&weights, 41);
    weights.add_multilinear(ext(7), (0..8).map(|i| ext(i + 9)).collect()).unwrap();
    check(&weights, 43);
    weights.add_tensor_factors(ext(19), (0..8).map(|i| ext(i + 21)).collect()).unwrap();
    check(&weights, 47);
    weights.add_product_pairs(ext(31), (0..8).map(|i| [ext(i + 33), ext(i + 51)]).collect()).unwrap();
    check(&weights, 53);
    weights.add_line_m31_tensor(ext(61), M31(7)).unwrap();
    weights.add_line_m31_batch(&[ext(71), ext(81)], &[M31(11), M31(13)]).unwrap();
    check(&weights, 59);
}

#[test]
fn actual_round_zero_component_shapes_at_log_eight() {
    // The production pre-query representation consists of three multilinear
    // components, the deferred binary mask, and two circle-tensor components.
    // Arbitrary validated tensor factors exercise that same constructor.
    let mut weights = WeightAccumulator::empty(10);
    for row in 0..3 {
        weights.add_multilinear(ext(10 + row),
            (0..10).map(|i| ext(30 + i + 17 * row)).collect()).unwrap();
    }
    let masks: [u16; 64] = core::array::from_fn(|i| ((i as u16) * 977) ^ 0x55aa);
    weights.add_grouped_64x16_binary_masks_deferred(masks).unwrap();
    for sample in 0..2 {
        weights.add_tensor_factors(ext(100 + sample),
            (0..10).map(|i| ext(120 + i + sample * 29)).collect()).unwrap();
    }
    weights.fold_deferred_relation_arity4(ext(211));
    check(&weights, 223);
}

#[test]
fn deferred_mask_after_round_zero_matches_exact_dual_order() {
    for mask in [0u16, 1, 2, 4, 8, 0x55aa, 0x8000, 0xffff] {
        let mut weights = WeightAccumulator::empty(10);
        weights.add_grouped_64x16_binary_masks_deferred([mask; 64]).unwrap();
        let alpha = ext(17);
        weights.fold_deferred_relation_arity4(alpha);
        let alpha2 = alpha.mul(alpha);
        let powers = [QM31::ONE, alpha2.mul(alpha), alpha2, alpha];
        for index in 0..256u32 {
            let chunk = index % 4;
            let mut expected = QM31::ZERO;
            for slot in 0..4u32 {
                if mask & (1u16 << (4 * chunk + slot)) != 0 {
                    expected = expected.add(powers[slot as usize]);
                }
            }
            expected = expected.mul(q(536_870_912)); // 1/4 in M31
            assert_eq!(weights.weight_at(index), expected);
        }
        check(&weights, 227);
    }
}

#[test]
fn snapshot_copies_metadata_and_uses_full_discrepancy() {
    let mut weights = WeightAccumulator::empty(8);
    weights.add_geometric(QM31::ONE, QM31::ONE);
    let values = coefficients(41);
    let queries = core::array::from_fn(|i| (i as u32) * 17);
    let view = V6QueryBatchPrechallengeView {
        transcript_state: [0x5a; 32], running_claim: ext(23), weights: &weights,
        gamma: ext(29), alpha0: ext(31), final256_coefficients: &values,
        queries, selector: 0, compact_counter: 3, frontier_nodes: 203,
    };
    let got = snapshot_query_batch_prechallenge(&view);
    assert_eq!(got.terminal_discrepancy, view.running_claim.sub(direct(&weights, &values)));
    assert_eq!(got.transcript_state, view.transcript_state);
    assert_eq!(got.running_claim, view.running_claim);
    assert_eq!(got.gamma, view.gamma);
    assert_eq!(got.alpha0, view.alpha0);
    assert_eq!(got.queries, view.queries);
    assert_eq!(got.selector, view.selector);
    assert_eq!(got.compact_counter, view.compact_counter);
    assert_eq!(got.frontier_nodes, view.frontier_nodes);
}

#[test]
fn production_terminal_dot_remains_a_separate_four_entry_operation() {
    let mut weights = WeightAccumulator::empty(2);
    weights.add_geometric(q(3), q(5));
    weights.add_line_m31_tensor(ext(2), M31(7)).unwrap();
    weights.add_line_m31_batch(&[ext(11), ext(13)], &[M31(17), M31(19)]).unwrap();
    let values = [ext(23), ext(29), ext(31), ext(37)];
    let expected = (0..4).fold(QM31::ZERO,
        |sum, i| sum.add(values[i].mul(weights.weight_at(i as u32))));
    assert_eq!(weights.dot(&values), expected);
}
