//! Fixed-challenge compatible-image diagnostic, not a full privacy theorem.
use super::basis_transport::{transport, N};
use crate::circle_candidate::CircleEncoder;
use aspis_core::{
    circle::{secure_ood_circle_point_from_parameter, SecureCirclePoint},
    circle_fri::selected_circle_fiber_points_shared,
    field::{qm31_circle_to_line_fold4, CM31, M31, M31_HALF, QM31 as K},
    state_only_hiding::state_only_explicit_g_mask_factor,
    sumcheck::WeightAccumulator,
    v6_onefold::evaluate_final256_coefficients,
    v6_transcript::v6_statement_points,
};

pub(super) fn sample(i: u32) -> K {
    K {
        c0: CM31::new(M31(i + 1), M31(3 * i + 7)),
        c1: CM31::new(M31(5 * i + 11), M31(7 * i + 13)),
    }
}
fn sc(i: usize) -> K {
    K::from_cm31(CM31::from_m31(M31(i as u32)))
}

// Primal of the retained inactive_row_binding::edges/xt natural-basis map.
pub(super) fn times_x(v: &[K]) -> Vec<K> {
    let mut out = vec![K::ZERO; v.len() + 1];
    for (j, &value) in v.iter().enumerate() {
        let (mut row, mut bit, mut scale) = (j, 0, M31::ONE);
        while row & (1 << bit) != 0 {
            row ^= 1 << bit;
            scale = scale.mul(M31_HALF);
            out[row] = out[row].add(value.mul_m31(scale));
            bit += 1;
        }
        out[row | (1 << bit)] = out[row | (1 << bit)].add(value.mul_m31(scale));
    }
    out
}
pub(super) fn chord_product(q: &[K], [a, b, c]: [K; 3]) -> Vec<K> {
    let even: Vec<_> = q.chunks_exact(2).map(|v| v[0]).collect();
    let odd: Vec<_> = q.chunks_exact(2).map(|v| v[1]).collect();
    let xe = times_x(&even);
    let xo = times_x(&odd);
    let xxo = times_x(&xo);
    let get = |v: &[K], i| v.get(i).copied().unwrap_or(K::ZERO);
    let mut out = vec![K::ZERO; 1028];
    for i in 0..514 {
        out[2 * i] = a
            .mul(get(&even, i))
            .add(b.mul(get(&xe, i)))
            .add(c.mul(get(&odd, i).sub(get(&xxo, i))));
        out[2 * i + 1] = c
            .mul(get(&even, i))
            .add(a.mul(get(&odd, i)))
            .add(b.mul(get(&xo, i)));
    }
    assert!(
        out[1024..].iter().all(|v| *v == K::ZERO),
        "source image constraints"
    );
    out.truncate(N);
    out
}
pub(super) fn eval_ood(c: &[(usize, K)], p: SecureCirclePoint) -> K {
    let mut factors = [K::ZERO; 10];
    factors[0] = p.y;
    factors[1] = p.x;
    for bit in 2..10 {
        factors[bit] = factors[bit - 1].square().mul_m31(M31(2)).sub(K::ONE);
    }
    c.iter().fold(K::ZERO, |s, &(j, v)| {
        s.add(
            (0..10)
                .filter(|&bit| j & (1 << bit) != 0)
                .fold(v, |v, bit| v.mul(factors[bit])),
        )
    })
}
pub(super) fn sparse(v: &[K]) -> Vec<(usize, K)> {
    v.iter()
        .copied()
        .enumerate()
        .filter(|(_, v)| *v != K::ZERO)
        .collect()
}

#[test]
fn r16_g_posterior_including_final256_compatible_image() {
    assert_eq!(compatible_image(Placement::Original), 408);
}

#[test]
fn r17_structured_g_first271_negative_compatible_image() {
    // Preserve the failed candidate: 56 additional constraints beyond the
    // 22 mandatory fold relations. This is not a repaired-source theorem.
    let rank = compatible_image(Placement::First271);
    assert_eq!(rank, 540);
    assert!(rank < 618 - 22);
}

#[test]
fn r17_structured_g_vandermonde_compatible_image() {
    assert_eq!(compatible_image(Placement::Vandermonde), 596);
}

#[test]
fn r17_structured_g_first_relation_compatible_image() {
    assert_eq!(compatible_image(Placement::VandermondeRelation), 601);
}

#[derive(Clone, Copy, Debug)]
enum Placement {
    Original,
    First271,
    Vandermonde,
    VandermondeRelation,
    VandermondeJoint,
    SparseCodeRelation,
    SparseCodeJoint,
}

fn compatible_image(placement: Placement) -> usize {
    compatible_image_at(placement, None)
}

pub(super) struct PublicPrefix {
    pub(super) z: [K; 10],
    pub(super) kappa: K,
    pub(super) tau: K,
    pub(super) alpha: K,
    pub(super) p0: SecureCirclePoint,
    pub(super) p1: SecureCirclePoint,
    pub(super) queries: Vec<u32>,
}

#[test]
#[ignore = "requires accepted R17 host public-prefix audit log"]
fn r17_actual_source_prefix_compatible_image() {
    let (path, prefix) = read_public_prefix();
    assert_eq!(
        compatible_image_at(Placement::VandermondeRelation, Some(prefix)),
        601
    );
    println!("R17_ACTUAL_PREFIX compatible_rank=601 observations=624 source_log={path}");
}

#[test]
#[ignore = "requires accepted R17 host public-prefix audit log"]
fn r17_actual_source_prefix_joint_ready_image() {
    let (path, prefix) = read_public_prefix();
    assert_eq!(
        compatible_image_at(Placement::VandermondeJoint, Some(prefix)),
        601
    );
    println!("R17_JOINT_READY_PREFIX compatible_rank=601 observations=625 source_log={path}");
}

#[test]
#[ignore = "requires accepted R18 sparse-code source public-prefix audit log"]
fn r18_actual_source_prefix_sparse_code_relation() {
    let (path,prefix)=read_public_prefix();
    assert_eq!(compatible_image_at(Placement::SparseCodeRelation,Some(prefix)),601);
    println!("R18_SPARSE_CODE_PREFIX rank=601 observations=624 source_log={path}");
}

#[test]
#[ignore = "requires accepted R18 sparse-code source public-prefix audit log"]
fn r18_actual_source_prefix_sparse_code_joint() {
    let (path,prefix)=read_public_prefix();
    assert_eq!(compatible_image_at(Placement::SparseCodeJoint,Some(prefix)),601);
    println!("R18_SPARSE_CODE_PREFIX rank=601 observations=625 source_log={path}");
}

pub(super) fn read_public_prefix() -> (String, PublicPrefix) {
    let path = std::env::var("ASPIS_R17_PUBLIC_PREFIX_LOG").expect("explicit source audit log");
    let log = std::fs::read_to_string(&path).unwrap();
    assert!(log.lines().any(|l| l == "R17_PUBLIC_PREFIX_ACCEPTED"));
    let records: Vec<_> = log
        .lines()
        .filter_map(|l| l.strip_prefix("R17_PUBLIC_PREFIX "))
        .collect();
    assert_eq!(records.len(), 1, "one accepted source execution per audit");
    let record: serde_json::Value = serde_json::from_str(records[0]).unwrap();
    let bytes: Vec<u8> = serde_json::from_value(record["fields"].clone()).unwrap();
    assert_eq!(bytes.len(), 18 * 16);
    let fields: Vec<_> = bytes
        .chunks_exact(16)
        .map(|b| K::from_le_bytes(b).unwrap())
        .collect();
    let queries: Vec<u32> = serde_json::from_value(record["queries"].clone()).unwrap();
    assert_eq!(queries.len(), 22);
    let mut unique = queries.clone();
    unique.sort_unstable();
    unique.dedup();
    assert_eq!(unique.len(), 22);
    assert!(queries.iter().all(|&q| q < 1 << 18));
    assert_ne!(fields[17], K::ZERO, "source nonzero gamma");
    let prefix = PublicPrefix {
        z: fields[..10].try_into().unwrap(),
        kappa: fields[10],
        tau: fields[11],
        alpha: fields[12],
        p0: SecureCirclePoint {
            x: fields[13],
            y: fields[14],
        },
        p1: SecureCirclePoint {
            x: fields[15],
            y: fields[16],
        },
        queries,
    };
    for p in [prefix.p0, prefix.p1] {
        assert_eq!(p.x.square().add(p.y.square()), K::ONE);
    }
    assert_ne!(prefix.p0, prefix.p1);
    assert_ne!(prefix.kappa, K::ZERO);
    assert_ne!(prefix.tau, K::ZERO);
    (path, prefix)
}

fn compatible_image_at(placement: Placement, prefix: Option<PublicPrefix>) -> usize {
    let structured = !matches!(placement, Placement::Original);
    let sparse_code=matches!(placement,Placement::SparseCodeRelation|Placement::SparseCodeJoint);
    let has_terminal = matches!(placement, Placement::VandermondeJoint|Placement::SparseCodeJoint);
    let has_relation = matches!(
        placement,
        Placement::VandermondeRelation | Placement::VandermondeJoint
            | Placement::SparseCodeRelation | Placement::SparseCodeJoint
    );
    let PublicPrefix {
        z,
        alpha,
        p0,
        p1,
        kappa,
        tau,
        queries,
    } = prefix.unwrap_or_else(|| {
        let mut queries = vec![4u32, 6];
        queries.extend((0..20).map(|i| 1000 + 7919 * i));
        PublicPrefix {
            z: core::array::from_fn(|i| sample(i as u32 + 1)),
            alpha: sample(151),
            p0: secure_ood_circle_point_from_parameter(sample(71)).unwrap(),
            p1: secure_ood_circle_point_from_parameter(sample(113)).unwrap(),
            kappa: sample(191),
            tau: sample(211),
            queries,
        }
    });
    let abc = [
        p0.x.mul(p1.y).sub(p0.y.mul(p1.x)),
        p0.y.sub(p1.y),
        p1.x.sub(p0.x),
    ];
    assert!(abc[1] != K::ZERO || abc[2] != K::ZERO, "distinct OOD chord");
    let mut earlier = Vec::new();
    for round in 0..3 {
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
            earlier.push(
                (0..N)
                    .map(|r| {
                        let prefix = (0..round).fold(K::ONE, |v, bit| {
                            v.mul(if r >> (9 - bit) & 1 == 1 {
                                z[bit]
                            } else {
                                K::ONE.sub(z[bit])
                            })
                        });
                        prefix
                            .mul(if r >> suffix_bits & 1 == 1 {
                                sc(x)
                            } else {
                                K::ONE.sub(sc(x))
                            })
                            .mul(factors[r & ((1 << suffix_bits) - 1)])
                    })
                    .collect::<Vec<_>>(),
            );
        }
    }
    if structured {
        // Proposed (not source-instantiated) initial scalar plus 27 independent
        // zero-boundary polynomial coordinates per round. The triangular
        // semantic map is invertible, so use its underlying coin coordinates.
        earlier = (0..271)
            .map(|i| {
                if sparse_code {
                    let mut row=vec![K::ZERO;N];
                    row[transport().order[super::sparse_coded_g::slot(i)]]=K::ONE;
                    return row;
                }
                if matches!(
                    placement,
                    Placement::Vandermonde
                        | Placement::VandermondeRelation
                        | Placement::VandermondeJoint
                ) {
                    return super::structured_g::mixing_row(i);
                }
                (0..N)
                    .map(|j| if i == j { K::ONE } else { K::ZERO })
                    .collect()
            })
            .collect();
    }
    let mut point_weights: Vec<_> = v6_statement_points(&z)
        .into_iter()
        // The proposed first G claim is the structured polynomial evaluation,
        // already determined by the 271 coins. Retain the other two MLE claims.
        .skip(usize::from(structured))
        .map(|p| {
            let mut w = WeightAccumulator::empty(10);
            w.add_multilinear(K::ONE, p.to_vec()).unwrap();
            (0..N).map(|r| w.weight_at(r as u32)).collect::<Vec<_>>()
        })
        .collect();
    let selected_mask=|| {
        if !sparse_code {return super::structured_g::mask_weights(&z);}
        let mut coins=vec![K::ZERO;271];let mut out=vec![K::ZERO;N];
        super::sparse_coded_g::original_weights_into(&z,
            transport().order.as_slice().try_into().unwrap(),&mut coins,&mut out);
        out
    };
    if has_terminal {
        // This field is serialized, even though it is determined by the
        // G coin coordinates. Keep its compatibility equation explicit
        // before attempting joint H1/G composition.
        point_weights.insert(0, selected_mask());
    }
    let pts = selected_circle_fiber_points_shared(20, &queries).unwrap();
    let enc = CircleEncoder::new_for_domain_log(20);
    let eval: Vec<Vec<_>> = queries
        .iter()
        .flat_map(|&id| (0..4).map(move |slot| 4 * id as usize + slot))
        .map(|pos| {
            (0..N)
                .map(|j| enc.encode_c1_basis_value(j, pos).unwrap())
                .collect()
        })
        .collect();
    // 82 earlier + 88 raw + 3 original-row points + 256 final coefficients
    // + the source's publicly serialized inactive-sum claim.
    // OOD is fixed at zero by parametrizing c=L*q with the source image gate.
    let raw_start = earlier.len();
    let point_start = raw_start + 88;
    let final_start = point_start + point_weights.len();
    let inactive_index = final_start + 256;
    let mut matrix =
        vec![vec![K::ZERO; 1022]; inactive_index + 1 + if has_relation { 6 } else { 0 }];
    let original = has_relation.then(|| {
        if !sparse_code {return super::two_channel::original_weights(&z,kappa,true);}
        let mut ordinary=super::two_channel::original_weights(&z,kappa,false);
        let mut first=WeightAccumulator::empty(10);
        first.add_multilinear(K::ONE,v6_statement_points(&z)[0].to_vec()).unwrap();
        let mask=selected_mask();
        for i in 0..N {ordinary[i]=ordinary[i].add(kappa.mul(mask[i].sub(first.weight_at(i as u32))));}
        ordinary
    });
    let relation=has_relation.then(|| {
        if !sparse_code {return super::two_channel::quotient_weights(&z,kappa,abc,tau,true);}
        let mut v=super::two_channel::chord_transpose(&transport().dual(original.as_ref().unwrap()),abc);
        v[1023]=v[1023].add(tau.pow(3));
        v[1022]=v[1022].add(tau.pow(4).mul(abc[1]));
        v[1021]=v[1021].sub(tau.pow(4).mul(abc[2]));
        let mut w=WeightAccumulator::empty(10);w.add_dense(v).unwrap();w
    });
    let folded_relation = relation.clone().map(|mut w| {
        w.fold_deferred_relation_arity4(alpha);
        w
    });
    if has_relation {
        // In the compact polynomial c4=claim/4-c0. The extra constraint
        // P(alpha)=dot(Final256,folded_weights) has coefficient alpha on
        // sent c1; at alpha=0 its coefficient on sent c0 is one instead.
        // Thus independence does not require rejecting zero fold challenges.
        assert!(alpha != K::ZERO || K::ONE.sub(alpha.pow(4)) != K::ZERO);
    }
    // Each fold equation has a nonzero coefficient in its own disjoint raw
    // block, so these 22 compatibility equations are independent.
    for pt in &pts {
        let weights: [K; 4] = core::array::from_fn(|slot| {
            let x = if slot < 2 { pt.x } else { pt.x.neg() };
            let y = if slot == 0 || slot == 3 {
                pt.y
            } else {
                pt.y.neg()
            };
            let mut unit = [K::ZERO; 4];
            unit[slot] = abc[0].add(abc[1].mul_m31(x)).add(abc[2].mul_m31(y)).inv();
            qm31_circle_to_line_fold4(unit, alpha, pt.x.double().inv(), pt.y.double().inv())
        });
        assert!(weights.iter().any(|w| *w != K::ZERO));
    }
    for col in 0..1022 {
        let mut q = vec![K::ZERO; N];
        if col < 1021 {
            q[col] = K::ONE;
        } else {
            q[1021] = abc[1];
            q[1022] = abc[2];
        }
        assert_eq!(q[1023], K::ZERO);
        assert_eq!(abc[1].mul(q[1022]).sub(abc[2].mul(q[1021])), K::ZERO);
        let c = chord_product(&q, abc);
        let cs = sparse(&c);
        let qs = sparse(&q);
        assert_eq!(eval_ood(&cs, p0), K::ZERO);
        assert_eq!(eval_ood(&cs, p1), K::ZERO);
        let m = transport().inverse(&c);
        assert_eq!(transport().forward(&m), c);
        let ms = sparse(&m);
        matrix[inactive_index][col] = m
            .iter()
            .enumerate()
            .filter(|(r, _)| transport().inactive[*r])
            .fold(K::ZERO, |s, (_, v)| s.add(*v));
        assert_eq!(matrix[inactive_index][col], c[1023]);
        for i in 0..earlier.len() {
            matrix[i][col] = ms
                .iter()
                .fold(K::ZERO, |s, &(r, v)| s.add(earlier[i][r].mul(v)));
        }
        for i in 0..88 {
            matrix[raw_start + i][col] = cs
                .iter()
                .fold(K::ZERO, |s, &(j, v)| s.add(v.mul_m31(eval[i][j])));
            let qval = qs
                .iter()
                .fold(K::ZERO, |s, &(j, v)| s.add(v.mul_m31(eval[i][j])));
            let pt = pts[i / 4];
            let x = if i % 4 < 2 { pt.x } else { pt.x.neg() };
            let y = if i % 4 == 0 || i % 4 == 3 {
                pt.y
            } else {
                pt.y.neg()
            };
            assert_eq!(
                matrix[raw_start + i][col],
                qval.mul(abc[0].add(abc[1].mul_m31(x)).add(abc[2].mul_m31(y)))
            );
        }
        for i in 0..point_weights.len() {
            matrix[point_start + i][col] = ms
                .iter()
                .fold(K::ZERO, |s, &(r, v)| s.add(point_weights[i][r].mul(v)));
        }
        if has_terminal {
            let coins: [K; 271] = core::array::from_fn(|i| matrix[i][col]);
            assert_eq!(
                matrix[point_start][col],
                super::structured_g::mask_eval(&coins, &z)
            );
            // Its coefficient on the first G point is one; the 22 fold
            // equations have no point/coin coefficients. The relation
            // equation has a nonzero sent-polynomial coefficient. Hence
            // all 24 equations remain independent.
        }
        let finals: Vec<_> = q
            .chunks_exact(4)
            .map(|v| v[0].add(alpha.mul(v[1].add(alpha.mul(v[2].add(alpha.mul(v[3])))))))
            .collect();
        for i in 0..256 {
            matrix[final_start + i][col] = finals[i];
        }
        if let Some(weights) = &relation {
            let polynomial = aspis_core::sumcheck::polynomial_for_extension(&q, weights);
            let claim = ms.iter().fold(K::ZERO, |s, &(i, v)| {
                s.add(v.mul(original.as_ref().unwrap()[i]))
            });
            assert_eq!(aspis_core::sumcheck::boundary_sum(&polynomial), claim);
            let expected = finals.iter().enumerate().fold(K::ZERO, |s, (i, &v)| {
                s.add(v.mul(folded_relation.as_ref().unwrap().weight_at(i as u32)))
            });
            assert_eq!(aspis_core::sumcheck::evaluate(&polynomial, alpha), expected);
            // Literal compact relation wire order: c0,c1,c2,c3,c5,c6 (not
            // the semantic polynomial's c0,c2,...,c27 convention).
            for (i, j) in [0, 1, 2, 3, 5, 6].into_iter().enumerate() {
                matrix[inactive_index + 1 + i][col] = polynomial[j];
            }
        }
        for (i, pt) in pts.iter().enumerate() {
            let qvalues = core::array::from_fn(|slot| {
                let x = if slot < 2 { pt.x } else { pt.x.neg() };
                let y = if slot == 0 || slot == 3 {
                    pt.y
                } else {
                    pt.y.neg()
                };
                matrix[raw_start + 4 * i + slot][col]
                    .mul(abc[0].add(abc[1].mul_m31(x)).add(abc[2].mul_m31(y)).inv())
            });
            assert_eq!(
                qm31_circle_to_line_fold4(qvalues, alpha, pt.x.double().inv(), pt.y.double().inv()),
                evaluate_final256_coefficients(&finals, pt.x.mul(pt.x).double().sub(M31::ONE))
                    .unwrap()
            );
        }
    }
    let n = matrix.len();
    let mut a = matrix.clone();
    let mut u = vec![vec![K::ZERO; n]; n];
    for i in 0..n {
        u[i][i] = K::ONE;
    }
    let mut pivots = Vec::new();
    for col in 0..1022 {
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
                if f == K::ZERO {
                    continue;
                }
                for j in col..1022 {
                    a[r][j] = a[r][j].sub(f.mul(ar[j]));
                }
                for j in 0..n {
                    u[r][j] = u[r][j].sub(f.mul(ur[j]));
                }
            }
        }
        pivots.push(col);
    }
    let rank = pivots.len();
    let consistency = 22 + usize::from(has_relation) + usize::from(has_terminal);
    println!(
        "FINAL_POSTERIOR placement={placement:?} rows={n} variables=1022 rank={rank} expected_consistency_relations={consistency}"
    );
    assert!(rank <= n - consistency);
    assert!(a[rank..].iter().flatten().all(|v| *v == K::ZERO));
    // Independent lower-rank certificate: U_top * original pivot columns = I.
    for i in 0..rank {
        for j in 0..rank {
            let value = (0..n).fold(K::ZERO, |s, k| s.add(u[i][k].mul(matrix[k][pivots[j]])));
            assert_eq!(value, if i == j { K::ONE } else { K::ZERO });
        }
    }
    rank
}
