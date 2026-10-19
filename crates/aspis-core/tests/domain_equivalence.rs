use aspis_core::fast_domain;
use aspis_core::r0::domain::{
    fibre_point as reference_fibre_point, line_node as reference_line_node, FibreIndex,
};
use aspis_core::r0::FIBRE_COUNT;

#[test]
fn every_fibre_point_matches_reference_and_is_on_circle() {
    for index in 0..FIBRE_COUNT {
        let checked = FibreIndex::new(index).expect("index is within FIBRE_COUNT");
        let actual = fast_domain::fibre_point(checked);
        let expected = reference_fibre_point(checked);
        assert_eq!(actual, expected, "fibre point mismatch at index {index}");
        assert!(actual.is_on_circle(), "point is off circle at index {index}");
    }
}

#[test]
fn line_node_is_two_x_squared_minus_one() {
    for index in 0..FIBRE_COUNT {
        let checked = FibreIndex::new(index).expect("index is within FIBRE_COUNT");
        assert_eq!(
            fast_domain::line_node(checked),
            reference_line_node::<aspis_core::field::M31>(checked),
            "line node mismatch at index {index}"
        );
    }
}
