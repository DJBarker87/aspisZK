use aspis_core::r0::domain::{
    fibre_point as reference_fibre_point, line_node as reference_line_node, FibreIndex,
};
use aspis_core::r0::FIBRE_COUNT;
use aspis_r1_cost_probe::fast_domain;

#[test]
fn every_fibre_point_matches_reference_and_is_on_circle() {
    for index in 0..FIBRE_COUNT {
        let checked = FibreIndex::new(index).expect("index is within FIBRE_COUNT");
        let actual = fast_domain::fibre_point(checked);
        let expected = reference_fibre_point(checked);
        assert_eq!((actual.x, actual.y), (expected.x, expected.y), "fibre point mismatch at index {index}");
        assert!(actual.is_on_circle(), "point is off circle at index {index}");
    }
}

#[test]
fn every_line_node_matches_reference() {
    for index in 0..FIBRE_COUNT {
        let checked = FibreIndex::new(index).expect("index is within FIBRE_COUNT");
        assert_eq!(
            fast_domain::line_node(checked),
            reference_line_node::<aspis_core::field::M31>(checked),
            "line node mismatch at index {index}"
        );
    }
}
