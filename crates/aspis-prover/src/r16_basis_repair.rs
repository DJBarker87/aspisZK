//! Candidate only: reversible public basis transport, not a privacy theorem.
use crate::{
    circle_candidate::CircleEncoder,
    v8_privacy_affine_gate::{certify_fixed_affine, AffineCertificate},
};
use aspis_core::field::M31;
#[path = "../../../docs/research/v8-full-view-zk-20260912/tools/r16_basis_transport.rs"]
mod basis_transport;
use basis_transport::{Transport, N, PADS, PIVOT};

/// Fixed affine diagnostic, NOT the adaptive full transcript. In particular
/// the semantic messages, H1/C2 correlation, Final256 and oracle law are absent.
#[test]
fn r16_joint_raw_point_ood_same_coin_diagnostic() {
    use aspis_core::{
        circle::secure_ood_circle_point_from_parameter,
        field::{CM31, QM31 as K},
        sumcheck::WeightAccumulator,
        v6_transcript::v6_statement_points,
    };
    use aspis_statement::pool_v1::pool_v1_pair_forest_relation_free_mask_cells_v1;
    let sample = |i: u32| K {
        c0: CM31::new(M31(i + 1), M31(3 * i + 7)),
        c1: CM31::new(M31(5 * i + 11), M31(7 * i + 13)),
    };
    let limbs = |v: K| [v.c0.a, v.c0.b, v.c1.a, v.c1.b];
    let t = basis_transport::transport();
    let encoder = CircleEncoder::new_for_domain_log(20);
    let mut index = vec![0; N];
    for (j, &r) in t.order.iter().enumerate() {
        index[r] = j;
    }
    let mut queries = vec![4usize, 6];
    queries.extend((0..20).map(|i| 1000 + 7919 * i));
    let points = v6_statement_points(&core::array::from_fn(|i| sample(i as u32 + 1)));
    let mle = |p: &[K; 10], r: usize| {
        (0..10).fold(K::ONE, |v, bit| {
            v.mul(if (r >> (9 - bit)) & 1 == 1 {
                p[bit]
            } else {
                K::ONE.sub(p[bit])
            })
        })
    };
    let ood: Vec<_> = [sample(71), sample(113)]
        .into_iter()
        .map(|parameter| {
            let p = secure_ood_circle_point_from_parameter(parameter).unwrap();
            let mut factors = [K::ZERO; 10];
            factors[0] = p.y;
            factors[1] = p.x;
            for i in 2..10 {
                factors[i] = factors[i - 1].square().mul_m31(M31(2)).sub(K::ONE);
            }
            factors
        })
        .collect();
    for p in &points {
        let mut source_weights = WeightAccumulator::empty(10);
        source_weights.add_multilinear(K::ONE, p.to_vec()).unwrap();
        for r in 0..N {
            assert_eq!(mle(p, r), source_weights.weight_at(r as u32));
        }
    }
    let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    for column in 0usize..16 {
        let rows: Vec<_> = cells
            .iter()
            .filter(|cell| {
                usize::from(cell.column) == column
                    && usize::from(cell.row) != PIVOT
                    && !(column == 3 && usize::from(cell.row) == 1014)
            })
            .map(|cell| usize::from(cell.row))
            .collect();
        let mut matrix = vec![vec![M31::ZERO; rows.len()]; 108];
        for (k, &r) in rows.iter().enumerate() {
            // T sends every legal unit/balanced-unit direction to this
            // single coefficient. The point disclosures still use old rows.
            let j = index[r];
            let mut delta = vec![M31::ZERO; N];
            delta[r] = M31::ONE;
            if t.inactive[r] {
                delta[PIVOT] = M31::ONE.neg();
            }
            let mut expected = vec![M31::ZERO; N];
            expected[j] = M31::ONE;
            assert_eq!(t.forward(&delta), expected);
            for (q, &query) in queries.iter().enumerate() {
                for slot in 0..4 {
                    matrix[4 * q + slot][k] =
                        encoder.encode_c1_basis_value(j, 4 * query + slot).unwrap();
                }
            }
            for (a, p) in points.iter().enumerate() {
                let value = if t.inactive[r] {
                    mle(p, r).sub(mle(p, PIVOT))
                } else {
                    mle(p, r)
                };
                for (b, limb) in limbs(value).into_iter().enumerate() {
                    matrix[88 + 4 * a + b][k] = limb;
                }
            }
            for (a, factors) in ood.iter().enumerate() {
                let value = (0..10)
                    .filter(|&bit| j & (1 << bit) != 0)
                    .fold(K::ONE, |v, bit| v.mul(factors[bit]));
                for (b, limb) in limbs(value).into_iter().enumerate() {
                    matrix[100 + 4 * a + b][k] = limb;
                }
            }
        }
        let identity: Vec<Vec<_>> = (0..108)
            .map(|i| {
                (0..108)
                    .map(|j| if i == j { M31::ONE } else { M31::ZERO })
                    .collect()
            })
            .collect();
        // The raw-only 89-direction argument cannot be reused as 108 fresh
        // directions. Keep an explicit verified separator for this misuse.
        let first_pads: Vec<_> = t.order[..PADS]
            .iter()
            .map(|r| rows.iter().position(|row| row == r).unwrap())
            .collect();
        let restricted: Vec<Vec<_>> = matrix
            .iter()
            .map(|row| first_pads.iter().map(|&k| row[k]).collect())
            .collect();
        match certify_fixed_affine(&restricted, &identity).unwrap() {
            AffineCertificate::Separator { rank, .. } => assert!(rank <= PADS),
            _ => panic!("raw-only pads were incorrectly credited with full joint coverage"),
        }
        let certificate = certify_fixed_affine(&matrix, &identity).unwrap();
        match certificate {
            AffineCertificate::Correction { rank, .. } => {
                println!("R16_JOINT column={column} observations=108 masks={} rank={rank}", rows.len());
                assert_eq!(rank, 108);
            }
            AffineCertificate::Separator { rank, target_column, nonzero, .. } =>
                panic!("joint diagnostic obstruction: column={column} rank={rank} target={target_column} nonzero={nonzero:?}"),
        }
    }
}

#[test]
fn r16_source_low_factors_match_four_slot_polynomial_channels() {
    use aspis_core::circle_fri::selected_circle_fiber_points_shared;
    let encoder = CircleEncoder::new_for_domain_log(20);
    let mut roots = Vec::with_capacity(1 << 18);
    for start in (0u32..1 << 18).step_by(512) {
        let ids: Vec<_> = (start..start + 512).collect();
        let points = selected_circle_fiber_points_shared(20, &ids).unwrap();
        for (&id, p) in ids.iter().zip(points) {
            let root = p.x.mul(p.x).double().sub(M31::ONE);
            roots.push(root.0);
            for (slot, (x, y)) in [
                (p.x, p.y),
                (p.x, p.y.neg()),
                (p.x.neg(), p.y.neg()),
                (p.x.neg(), p.y),
            ]
            .into_iter()
            .enumerate()
            {
                let index = 4 * id as usize + slot;
                assert_eq!(encoder.encode_c1_basis_value(1, index).unwrap(), y);
                assert_eq!(encoder.encode_c1_basis_value(2, index).unwrap(), x);
                let mut factor = root;
                for bit in 2..7 {
                    assert_eq!(
                        encoder.encode_c1_basis_value(1 << bit, index).unwrap(),
                        factor
                    );
                    factor = factor.mul(factor).double().sub(M31::ONE);
                }
            }
        }
    }
    roots.sort_unstable();
    roots.dedup();
    assert_eq!(
        roots.len(),
        1 << 18,
        "all source fibre line roots must be distinct"
    );
}

fn dot(a: &[M31], b: &[M31]) -> M31 {
    a.iter()
        .zip(b)
        .fold(M31::ZERO, |s, (a, b)| s.add(a.mul(*b)))
}

#[test]
fn r16_qm31_transport_preserves_dual_claims_and_batching() {
    use aspis_core::field::{CM31, QM31 as K};
    let t = basis_transport::transport();
    let sample = |i: u32| K {
        c0: CM31::new(M31(i + 1), M31(3 * i + 7)),
        c1: CM31::new(M31(5 * i + 11), M31(7 * i + 13)),
    };
    let w: Vec<_> = (0..N).map(|i| sample(i as u32)).collect();
    let dual = t.dual(&w);
    let qdot = |a: &[K], b: &[K]| a.iter().zip(b).fold(K::ZERO, |s, (a, b)| s.add(a.mul(*b)));
    let units = [
        K::ONE,
        K::from_cm31(CM31::new(M31::ZERO, M31::ONE)),
        K {
            c0: CM31::ZERO,
            c1: CM31::ONE,
        },
        K {
            c0: CM31::ZERO,
            c1: CM31::new(M31::ZERO, M31::ONE),
        },
    ];
    for unit in units {
        for r in 0..N {
            let mut m = vec![K::ZERO; N];
            m[r] = unit;
            let tm = t.forward(&m);
            assert_eq!(t.inverse(&tm), m);
            assert_eq!(qdot(&w, &m), qdot(&dual, &tm));
        }
    }
    let a: Vec<_> = (0..N).map(|i| sample(2 * i as u32 + 19)).collect();
    let b: Vec<_> = (0..N).map(|i| sample(3 * i as u32 + 23)).collect();
    let gamma = sample(101);
    let combined: Vec<_> = a
        .iter()
        .zip(&b)
        .map(|(a, b)| a.add(gamma.mul(*b)))
        .collect();
    let expected: Vec<_> = t
        .forward(&a)
        .iter()
        .zip(t.forward(&b))
        .map(|(a, b)| a.add(gamma.mul(b)))
        .collect();
    assert_eq!(t.forward(&combined), expected);
    assert_eq!(t.forward(&t.inverse(&a)), a);
}

#[test]
fn r16_transport_preserves_all_basis_vectors_and_dual_claims() {
    let t = Transport::new();
    let w: Vec<_> = (0..N).map(|i| M31((i * i + 17 * i + 3) as u32)).collect();
    let dual = t.dual(&w);
    for r in 0..N {
        let mut m = vec![M31::ZERO; N];
        m[r] = M31::ONE;
        let encoded = t.forward(&m);
        assert_eq!(t.inverse(&encoded), m);
        assert_eq!(dot(&w, &m), dot(&dual, &encoded));
    }
    for j in 0..PADS {
        let mut mask = vec![M31::ZERO; N];
        mask[t.order[j]] = M31::ONE;
        mask[PIVOT] = M31::ONE.neg();
        let mut expected = vec![M31::ZERO; N];
        expected[j] = M31::ONE;
        assert_eq!(t.forward(&mask), expected);
    }
}

#[test]
fn r16_known_bad_schedule_has_full_raw_mask_rank_after_transport() {
    let encoder = CircleEncoder::new_for_domain_log(20);
    let mut queries = vec![4usize, 6];
    queries.extend((0..20).map(|i| 1000 + 7919 * i));
    let mask: Vec<Vec<M31>> = queries
        .iter()
        .flat_map(|q| (0..4).map(move |s| 4 * q + s))
        .map(|index| {
            (0..PADS)
                .map(|j| encoder.encode_c1_basis_value(j, index).unwrap())
                .collect()
        })
        .collect();
    // Identity targets certify all 88 raw observation directions, not only
    // the selected-second fixture difference. This is still ONE schedule.
    let target: Vec<Vec<M31>> = (0..88)
        .map(|i| {
            (0..88)
                .map(|j| if i == j { M31::ONE } else { M31::ZERO })
                .collect()
        })
        .collect();
    match certify_fixed_affine(&mask, &target).unwrap() {
        AffineCertificate::Correction { rank, .. } => assert_eq!(rank, 88),
        other => panic!("candidate does not repair the retained schedule: {other:?}"),
    }
}
