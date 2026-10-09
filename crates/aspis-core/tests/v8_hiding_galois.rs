use aspis_core::{
    circle::secure_ood_circle_point_from_parameter,
    field::{CM31, M31, P, QM31},
    sumcheck::WeightAccumulator,
};

fn q(values: [u32; 4]) -> QM31 {
    QM31 {
        c0: CM31::new(M31(values[0]), M31(values[1])),
        c1: CM31::new(M31(values[2]), M31(values[3])),
    }
}

/// The current V8 validity checks admit distinct Frobenius-conjugate OOD
/// points.  For every one of the actual 1024 M31 natural-basis rows, the two
/// disclosed component evaluations then lie on the four-dimensional
/// Frobenius graph inside the eight-dimensional ambient `QM31 x QM31` view.
///
/// This is an exhaustive basis-row check of the source evaluator, not random
/// testing.  It refutes universal *ambient* rank 108 for the C1 raw block.  It
/// does not refute hiding: honest witness and mask evaluations obey the same
/// graph relation, which is why the Lean criterion uses legal-image
/// containment instead of ambient surjectivity.
#[test]
fn distinct_secure_frobenius_pair_makes_c1_ood_rows_dependent() {
    let parameter0 = q([17, 29, 43, 71]);
    let parameter1 = parameter0.pow(u64::from(P));
    assert_ne!(parameter0, parameter1);

    let point0 = secure_ood_circle_point_from_parameter(parameter0).unwrap();
    let point1 = secure_ood_circle_point_from_parameter(parameter1).unwrap();
    assert_ne!(point0, point1);
    assert_eq!(point1.x, point0.x.pow(u64::from(P)));
    assert_eq!(point1.y, point0.y.pow(u64::from(P)));

    let mut evaluation0 = WeightAccumulator::empty(10);
    evaluation0.add_circle_tensor(QM31::ONE, point0).unwrap();
    let mut evaluation1 = WeightAccumulator::empty(10);
    evaluation1.add_circle_tensor(QM31::ONE, point1).unwrap();

    for row in 0..1024u32 {
        assert_eq!(
            evaluation1.weight_at(row),
            evaluation0.weight_at(row).pow(u64::from(P)),
            "natural-basis row {row} violates Frobenius covariance"
        );
    }

    // `(0, 1)` is not on the graph of Frobenius, providing an explicit
    // ambient target that no M31-component evaluation pair can reach.
    assert_ne!(QM31::ONE, QM31::ZERO.pow(u64::from(P)));
}
