//! Tiny local observer regressions. These do not construct an accepting proof.
//! On the pinned code, offsets 4 and 255 are missed in release mode; in debug
//! mode the old helper violates WeightAccumulator::dot's length assertion.
#![cfg(feature = "aeneas-observer")]

use aspis_core::field::QM31;
use aspis_core::sumcheck::WeightAccumulator;
use aspis_core::v6_transcript::{
    snapshot_query_batch_prechallenge, V6QueryBatchPrechallengeView,
};

#[test]
fn prequery_snapshot_reads_all_256_coefficients() {
    // A geometric component with base one supplies the all-ones covector.
    let mut weights = WeightAccumulator::empty(8);
    weights.add_geometric(QM31::ONE, QM31::ONE);
    for index in [0usize, 3, 4, 255] {
        let mut values = [QM31::ZERO; 256];
        values[index] = QM31::ONE;
        let view = V6QueryBatchPrechallengeView {
            transcript_state: [7u8; 32],
            running_claim: QM31::ZERO,
            weights: &weights,
            gamma: QM31::ONE,
            alpha0: QM31::ONE,
            final256_coefficients: &values,
            queries: [0u32; 16],
            selector: 0,
            compact_counter: 0,
            frontier_nodes: 0,
        };
        let snapshot = snapshot_query_batch_prechallenge(&view);
        assert_eq!(
            snapshot.terminal_discrepancy,
            QM31::ZERO.sub(QM31::ONE),
            "pre-query snapshot omitted coefficient {index}",
        );
        assert_eq!(snapshot.transcript_state, view.transcript_state);
        assert_eq!(snapshot.running_claim, view.running_claim);
        assert_eq!(snapshot.gamma, view.gamma);
        assert_eq!(snapshot.alpha0, view.alpha0);
        assert_eq!(snapshot.queries, view.queries);
        assert_eq!(snapshot.selector, view.selector);
        assert_eq!(snapshot.compact_counter, view.compact_counter);
        assert_eq!(snapshot.frontier_nodes, view.frontier_nodes);
    }
}

#[test]
fn full_prequery_snapshot_preserves_zero_discrepancy() {
    let mut weights = WeightAccumulator::empty(8);
    weights.add_geometric(QM31::ONE, QM31::ONE);
    let mut values = [QM31::ZERO; 256];
    values[255] = QM31::ONE;
    let view = V6QueryBatchPrechallengeView {
        transcript_state: [0u8; 32],
        running_claim: QM31::ONE,
        weights: &weights,
        gamma: QM31::ONE,
        alpha0: QM31::ONE,
        final256_coefficients: &values,
        queries: [0u32; 16],
        selector: 0,
        compact_counter: 0,
        frontier_nodes: 0,
    };
    let snapshot = snapshot_query_batch_prechallenge(&view);
    assert_eq!(snapshot.terminal_discrepancy, QM31::ZERO);
}
