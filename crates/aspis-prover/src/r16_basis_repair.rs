//! Candidate only: reversible public basis transport, not a privacy theorem.
use crate::{
    circle_candidate::CircleEncoder,
    v8_privacy_affine_gate::{certify_fixed_affine, AffineCertificate},
};
use aspis_core::field::M31;
#[path = "../../../docs/research/v8-full-view-zk-20260912/tools/r16_basis_transport.rs"]
mod basis_transport;
use basis_transport::{Transport, N, PADS, PIVOT};
#[path = "r16_final_posterior.rs"]
mod final_posterior;

/// Mandatory quotient-opening/Final256 consistency, not independent privacy
/// targets. Checks both selected source maps on every coefficient basis unit.
#[test]
fn r16_final256_source_fold_consistency_all_basis_units() {
    use aspis_core::{
        circle_fri::selected_circle_fiber_points_shared,
        field::{qm31_circle_to_line_fold4, CM31, QM31 as K},
        v6_onefold::evaluate_final256_coefficients,
    };
    let alpha = K {
        c0: CM31::new(M31(2), M31(3)),
        c1: CM31::new(M31(5), M31(7)),
    };
    let powers = [K::ONE, alpha, alpha.square(), alpha.square().mul(alpha)];
    let mut queries = vec![4u32, 6];
    queries.extend((0..20).map(|i| 1000 + 7919 * i));
    let points = selected_circle_fiber_points_shared(20, &queries).unwrap();
    let encoder = CircleEncoder::new_for_domain_log(20);
    for coefficient in 0..N {
        let mut finals = vec![K::ZERO; 256];
        finals[coefficient / 4] = powers[coefficient % 4];
        for (&q, pt) in queries.iter().zip(&points) {
            let raw = core::array::from_fn(|slot| {
                K::from_cm31(CM31::from_m31(
                    encoder
                        .encode_c1_basis_value(coefficient, 4 * q as usize + slot)
                        .unwrap(),
                ))
            });
            let folded =
                qm31_circle_to_line_fold4(raw, alpha, pt.x.double().inv(), pt.y.double().inv());
            let root = pt.x.mul(pt.x).double().sub(M31::ONE);
            assert_eq!(
                folded,
                evaluate_final256_coefficients(&finals, root).unwrap(),
                "coefficient={coefficient} fibre={q}"
            );
        }
    }
}

/// Earlier semantic G responses and later G observations share all 1024
/// original G variables. Fixed challenges only; not a causal oracle theorem.
#[test]
fn r16_g_three_cut_and_later_view_same_coin_diagnostic() {
    use aspis_core::{
        circle::secure_ood_circle_point_from_parameter,
        field::{CM31, QM31 as K},
        state_only_hiding::state_only_explicit_g_mask_factor,
        sumcheck::WeightAccumulator,
        v6_transcript::v6_statement_points,
    };
    let sample = |i: u32| K {
        c0: CM31::new(M31(i + 1), M31(3 * i + 7)),
        c1: CM31::new(M31(5 * i + 11), M31(7 * i + 13)),
    };
    let sc = |i: usize| K::from_cm31(CM31::from_m31(M31(i as u32)));
    let z: [K; 10] = core::array::from_fn(|i| sample(i as u32 + 1));
    let mut matrix: Vec<Vec<K>> = Vec::new();
    for round in 0..3 {
        // Round 0's 28 evaluations encode (initial,27 compact coefficients).
        // Later rounds omit x=1: the earlier carried claim fixes that value.
        for x in (0..28).filter(|&x| round == 0 || x != 1) {
            let suffix_bits = 9 - round;
            let factors: Vec<_> = (0..1 << suffix_bits)
                .map(|suffix| {
                    let mut point = z;
                    point[round] = sc(x);
                    for bit in 0..suffix_bits {
                        point[round + 1 + bit] = sc((suffix >> (suffix_bits - 1 - bit)) & 1);
                    }
                    state_only_explicit_g_mask_factor(&point)
                })
                .collect();
            matrix.push(
                (0..N)
                    .map(|r| {
                        let prefix = (0..round).fold(K::ONE, |v, bit| {
                            v.mul(if r >> (9 - bit) & 1 == 1 {
                                z[bit]
                            } else {
                                K::ONE.sub(z[bit])
                            })
                        });
                        let current = if r >> suffix_bits & 1 == 1 {
                            sc(x)
                        } else {
                            K::ONE.sub(sc(x))
                        };
                        prefix
                            .mul(current)
                            .mul(factors[r & ((1 << suffix_bits) - 1)])
                    })
                    .collect(),
            );
        }
    }
    assert_eq!(matrix.len(), 82);
    let t = basis_transport::transport();
    let mut index = vec![0; N];
    for (j, &r) in t.order.iter().enumerate() {
        index[r] = j;
    }
    let pull = |coeff: &[K]| {
        (0..N)
            .map(|r| {
                if r != PIVOT && t.inactive[r] {
                    coeff[index[r]].add(coeff[PIVOT])
                } else {
                    coeff[index[r]]
                }
            })
            .collect::<Vec<_>>()
    };
    let encoder = CircleEncoder::new_for_domain_log(20);
    let mut queries = vec![4usize, 6];
    queries.extend((0..20).map(|i| 1000 + 7919 * i));
    for q in queries {
        for slot in 0..4 {
            let coeff: Vec<_> = (0..N)
                .map(|j| {
                    K::from_cm31(CM31::from_m31(
                        encoder.encode_c1_basis_value(j, 4 * q + slot).unwrap(),
                    ))
                })
                .collect();
            matrix.push(pull(&coeff));
        }
    }
    for p in v6_statement_points(&z) {
        let mut weights = WeightAccumulator::empty(10);
        weights.add_multilinear(K::ONE, p.to_vec()).unwrap();
        matrix.push((0..N).map(|r| weights.weight_at(r as u32)).collect());
    }
    for parameter in [sample(71), sample(113)] {
        let p = secure_ood_circle_point_from_parameter(parameter).unwrap();
        let mut factors = [K::ZERO; 10];
        factors[0] = p.y;
        factors[1] = p.x;
        for bit in 2..10 {
            factors[bit] = factors[bit - 1].square().mul_m31(M31(2)).sub(K::ONE);
        }
        let coeff: Vec<_> = (0..N)
            .map(|j| {
                (0..10)
                    .filter(|&bit| j & (1 << bit) != 0)
                    .fold(K::ONE, |v, bit| v.mul(factors[bit]))
            })
            .collect();
        matrix.push(pull(&coeff));
    }
    let n = matrix.len();
    assert_eq!(n, 175);
    let mut a = matrix.clone();
    let mut u = vec![vec![K::ZERO; n]; n];
    for i in 0..n {
        u[i][i] = K::ONE;
    }
    let mut pivots = Vec::new();
    for col in 0..N {
        let rank = pivots.len();
        if rank == n {
            break;
        }
        let Some(p) = (rank..n).find(|&r| a[r][col] != K::ZERO) else {
            continue;
        };
        a.swap(rank, p);
        u.swap(rank, p);
        let inv = a[rank][col].inv();
        for v in &mut a[rank] {
            *v = v.mul(inv);
        }
        for v in &mut u[rank] {
            *v = v.mul(inv);
        }
        let ar = a[rank].clone();
        let ur = u[rank].clone();
        for r in 0..n {
            if r != rank {
                let f = a[r][col];
                for c in col..N {
                    a[r][c] = a[r][c].sub(f.mul(ar[c]));
                }
                for c in 0..n {
                    u[r][c] = u[r][c].sub(f.mul(ur[c]));
                }
            }
        }
        pivots.push(col);
    }
    println!(
        "R16_G_JOINT earlier=82 later=93 variables=1024 rank={}",
        pivots.len()
    );
    assert_eq!(
        pivots.len(),
        n,
        "same-coin three-cut/later coverage obstruction"
    );
    // Independently verify the sparse right inverse, not just pivot count.
    for i in 0..n {
        for j in 0..n {
            let value = (0..n).fold(K::ZERO, |s, k| s.add(matrix[i][pivots[k]].mul(u[k][j])));
            assert_eq!(value, if i == j { K::ONE } else { K::ZERO });
        }
    }
}

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
