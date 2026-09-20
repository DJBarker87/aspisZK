//! Two-channel opening research. No production verifier or privacy verdict.
use super::{
    basis_transport::{transport, N},
    final_posterior::{chord_product, eval_ood, sample, sparse},
};
use crate::circle_candidate::CircleEncoder;
use aspis_core::{
    circle::secure_ood_circle_point_from_parameter,
    circle_fri::selected_circle_fiber_points_shared,
    field::{qm31_circle_to_line_fold4, M31, M31_HALF, QM31 as K},
    sumcheck::WeightAccumulator,
    v6_onefold::evaluate_final256_coefficients,
    v6_transcript::v6_statement_points,
};

fn dot(a: &[K], b: &[K]) -> K {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).fold(K::ZERO, |v, (&a, &b)| v.add(a.mul(b)))
}

pub(super) use super::opening_weights::{chord_transpose, original_weights, quotient_weights};

fn quotient_direction(col: usize, abc: [K; 3]) -> Vec<K> {
    let mut q = vec![K::ZERO; N];
    if col < 1021 {
        q[col] = K::ONE;
    } else {
        q[1021] = abc[1];
        q[1022] = abc[2];
    }
    q
}

// Returns an exact RREF and pivots; independently verifies a lower-rank
// certificate against the original matrix and the zero remaining rows.
fn reduce(matrix: &[Vec<K>]) -> (Vec<Vec<K>>, Vec<usize>) {
    let n = matrix.len();
    let width = matrix[0].len();
    assert!(matrix.iter().all(|r| r.len() == width));
    let mut a = matrix.to_vec();
    let mut u = vec![vec![K::ZERO; n]; n];
    for i in 0..n {
        u[i][i] = K::ONE;
    }
    let mut pivots = Vec::new();
    for col in 0..width {
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
            if r == rank || a[r][col] == K::ZERO {
                continue;
            }
            let f = a[r][col];
            for j in col..width {
                a[r][j] = a[r][j].sub(f.mul(ar[j]));
            }
            for j in 0..n {
                u[r][j] = u[r][j].sub(f.mul(ur[j]));
            }
        }
        pivots.push(col);
    }
    let rank = pivots.len();
    assert!(a[rank..].iter().flatten().all(|v| *v == K::ZERO));
    for i in 0..rank {
        for j in 0..rank {
            let v = (0..n).fold(K::ZERO, |s, k| s.add(u[i][k].mul(matrix[k][pivots[j]])));
            assert_eq!(v, if i == j { K::ONE } else { K::ZERO });
        }
    }
    (a, pivots)
}

#[test]
fn r17_h1_second_channel_final256_compatible_image() {
    let z = core::array::from_fn(|i| sample(i as u32 + 1));
    let alpha = sample(151);
    let p0 = secure_ood_circle_point_from_parameter(sample(71)).unwrap();
    let p1 = secure_ood_circle_point_from_parameter(sample(113)).unwrap();
    let mut queries = vec![4, 6];
    queries.extend((0..20).map(|i| 1000 + 7919 * i));
    h1_compatible_image(z, alpha, p0, p1, queries);
}

#[test]
#[ignore = "requires accepted R17 host public-prefix audit log"]
fn r17_actual_source_prefix_h1_compatible_image() {
    let (path, p) = super::final_posterior::read_public_prefix();
    h1_compatible_image(p.z, p.alpha, p.p0, p.p1, p.queries);
    println!("R17_ACTUAL_H1_PREFIX source_log={path}");
}

fn h1_compatible_image(
    z: [K; 10],
    alpha: K,
    p0: aspis_core::circle::SecureCirclePoint,
    p1: aspis_core::circle::SecureCirclePoint,
    queries: Vec<u32>,
) {
    let abc = [
        p0.x.mul(p1.y).sub(p0.y.mul(p1.x)),
        p0.y.sub(p1.y),
        p1.x.sub(p0.x),
    ];
    assert!(abc[1] != K::ZERO || abc[2] != K::ZERO);
    let active: Vec<_> = (0..N).filter(|&i| !transport().inactive[i]).collect();
    assert_eq!(active.len(), 214);
    // 214 active-row zeros plus one inactive-balance equation on m=T^-1(Lq).
    // With two OOD-zero constraints already parametrized, this should leave
    // 807 of the original 809 legal H1 pad directions.
    let nc = active.len() + 1;
    let mut constraints = vec![vec![K::ZERO; 1022]; nc];
    let point_weights: Vec<_> = v6_statement_points(&z)
        .into_iter()
        .map(|p| {
            let mut w = WeightAccumulator::empty(10);
            w.add_multilinear(K::ONE, p.to_vec()).unwrap();
            (0..N).map(|i| w.weight_at(i as u32)).collect::<Vec<_>>()
        })
        .collect();
    let pts = selected_circle_fiber_points_shared(20, &queries).unwrap();
    // Each fold equation has a nonzero coefficient in its own raw block.
    // The 22 constraints are therefore independent in observation space.
    for pt in &pts {
        assert_ne!(pt.x, M31::ZERO);
        assert_ne!(pt.y, M31::ZERO);
        let coefficients: [K; 4] = core::array::from_fn(|slot| {
            let x = if slot < 2 { pt.x } else { pt.x.neg() };
            let y = if slot == 0 || slot == 3 {
                pt.y
            } else {
                pt.y.neg()
            };
            let l = abc[0].add(abc[1].mul_m31(x)).add(abc[2].mul_m31(y));
            assert_ne!(l, K::ZERO);
            let mut unit = [K::ZERO; 4];
            unit[slot] = l.inv();
            qm31_circle_to_line_fold4(unit, alpha, pt.x.double().inv(), pt.y.double().inv())
        });
        assert!(coefficients.iter().any(|v| *v != K::ZERO));
    }
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
    // 88 raw + 3 original-row point claims + separate Final256.
    let mut observations = vec![vec![K::ZERO; 1022]; 347];
    for col in 0..1022 {
        let q = quotient_direction(col, abc);
        let c = chord_product(&q, abc);
        let cs = sparse(&c);
        assert_eq!(eval_ood(&cs, p0), K::ZERO);
        assert_eq!(eval_ood(&cs, p1), K::ZERO);
        let m = transport().inverse(&c);
        for (i, &r) in active.iter().enumerate() {
            constraints[i][col] = m[r];
        }
        constraints[nc - 1][col] = m
            .iter()
            .enumerate()
            .filter(|(i, _)| transport().inactive[*i])
            .fold(K::ZERO, |s, (_, v)| s.add(*v));
        assert_eq!(constraints[nc - 1][col], c[1023]);
        for i in 0..88 {
            observations[i][col] = cs
                .iter()
                .fold(K::ZERO, |s, &(j, v)| s.add(v.mul_m31(eval[i][j])));
        }
        for i in 0..3 {
            observations[88 + i][col] = dot(&m, &point_weights[i]);
        }
        let finals: Vec<_> = q
            .chunks_exact(4)
            .map(|v| v[0].add(alpha.mul(v[1].add(alpha.mul(v[2].add(alpha.mul(v[3])))))))
            .collect();
        for i in 0..256 {
            observations[91 + i][col] = finals[i];
        }
        for (i, pt) in pts.iter().enumerate() {
            let values = core::array::from_fn(|slot| {
                let x = if slot < 2 { pt.x } else { pt.x.neg() };
                let y = if slot == 0 || slot == 3 {
                    pt.y
                } else {
                    pt.y.neg()
                };
                let l = abc[0].add(abc[1].mul_m31(x)).add(abc[2].mul_m31(y));
                assert_ne!(l, K::ZERO);
                observations[4 * i + slot][col].mul(l.inv())
            });
            assert_eq!(
                qm31_circle_to_line_fold4(values, alpha, pt.x.double().inv(), pt.y.double().inv()),
                evaluate_final256_coefficients(&finals, pt.x.mul(pt.x).double().sub(M31::ONE))
                    .unwrap()
            );
        }
    }
    let (cr, pivots) = reduce(&constraints);
    assert_eq!(pivots.len(), 215);
    let mut kernel_count = 0;
    for free in (0..1022).filter(|i| !pivots.contains(i)) {
        let mut x = vec![K::ZERO; 1022];
        x[free] = K::ONE;
        for (r, &p) in pivots.iter().enumerate() {
            x[p] = cr[r][free].neg();
        }
        let mut q = x[..1021].to_vec();
        q.extend([abc[1].mul(x[1021]), abc[2].mul(x[1021]), K::ZERO]);
        let pad = transport().inverse(&chord_product(&q, abc));
        let mut h = vec![K::ZERO; N];
        crate::state_only_hiding::apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut h, &pad)
            .unwrap();
        assert_eq!(h, pad);
        kernel_count += 1;
    }
    assert_eq!(kernel_count, 807);
    let mut joint = constraints;
    joint.extend(observations);
    let (_, combined_pivots) = reduce(&joint);
    let image_rank = combined_pivots.len() - pivots.len();
    println!("R17_H1_SECOND_CHANNEL variables=1022 constraints=215 kernel=807 observation_rows=347 image_rank={image_rank} expected_fold_relations=22");
    assert_eq!(image_rank, 325, "extra H1 second-channel obstruction");
}

fn fold_coefficients(q: &[K], alpha: K) -> Vec<K> {
    q.chunks_exact(4)
        .map(|v| v[0].add(alpha.mul(v[1].add(alpha.mul(v[2].add(alpha.mul(v[3])))))))
        .collect()
}

/// Explicit polynomial-factor kernel. No dense 1022-column nullspace solve.
#[test]
#[ignore = "requires accepted R17 host public-prefix audit log"]
fn r17_actual_prefix_factor_kernel_reduced_maps() {
    let (_,p)=super::final_posterior::read_public_prefix();
    let pts=selected_circle_fiber_points_shared(20,&p.queries).unwrap();
    let roots:Vec<_>=pts.iter().map(|pt|pt.x.mul(pt.x).double().sub(M31::ONE)).collect();
    assert_eq!(roots.len(),22);
    let mut distinct=roots.clone();distinct.sort_by_key(|v|v.0);distinct.dedup();
    assert_eq!(distinct.len(),roots.len(),"distinct source fibre roots");
    let abc=[p.p0.x.mul(p.p1.y).sub(p.p0.y.mul(p.p1.x)),p.p0.y.sub(p.p1.y),p.p1.x.sub(p.p0.x)];
    assert!(abc[1]!=K::ZERO || abc[2]!=K::ZERO);
    let normal=abc[1].square().add(abc[2].square());
    assert_ne!(normal,K::ZERO,"distinct circle secant normal");
    let mut factor=vec![K::ONE];
    for &root in &roots {
        let mut next=super::final_posterior::times_x(&factor);
        for i in 0..factor.len(){next[i]=next[i].sub(factor[i].mul_m31(root));}
        factor=next;
    }
    assert_eq!(factor.len(),23);assert_ne!(factor[22],K::ZERO);
    let point:Vec<Vec<K>>=v6_statement_points(&p.z).iter().map(|z|{
        let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,z.to_vec()).unwrap();
        (0..1024).map(|i|w.weight_at(i)).collect()
    }).collect();
    let gp=super::structured_g::mask_weights(&p.z);
    let mix:Vec<_>=(0..271).map(super::structured_g::mixing_row).collect();
    let gw=quotient_weights(&p.z,p.kappa,abc,p.tau,true);
    let active:Vec<_>=(0..1024).filter(|&r|!transport().inactive[r]).collect();assert_eq!(active.len(),214);
    let mut hm=vec![vec![];218];let mut gm=vec![vec![];281];
    let mut combined=vec![K::ZERO;1024];let mut last_pivot=None;let mut count=0;
    for degree in 22..=255 {
        assert_eq!(factor.len(),degree+1);assert_ne!(factor[degree],K::ZERO);
        let mut padded=factor.clone();padded.resize(256,K::ZERO);
        for &root in &roots{assert_eq!(evaluate_final256_coefficients(&padded,root).unwrap(),K::ZERO);}
        let scales=if degree<255{vec![[K::ONE,K::ZERO,K::ZERO],[K::ZERO,K::ONE,K::ZERO],[K::ZERO,K::ZERO,K::ONE]]}
            else{vec![[abc[1],abc[2],K::ZERO]]};
        for scale in scales {
            let mut q=vec![K::ZERO;1024];
            for i in 0..=degree {
                let b=factor[i].mul(scale[0]);let c=factor[i].mul(scale[1]);let d=factor[i].mul(scale[2]);
                q[4*i]=p.alpha.mul(b).add(p.alpha.square().mul(c)).add(p.alpha.pow(3).mul(d)).neg();
                q[4*i+1]=b;q[4*i+2]=c;q[4*i+3]=d;
            }
            // Increasing last nonzero coordinates certify independence.
            let pivot=q.iter().rposition(|&v|v!=K::ZERO).unwrap();
            if let Some(prev)=last_pivot{assert!(pivot>prev);}last_pivot=Some(pivot);
            assert_eq!(q[1023],K::ZERO);assert_eq!(abc[1].mul(q[1022]),abc[2].mul(q[1021]));
            assert!(fold_coefficients(&q,p.alpha).iter().all(|&v|v==K::ZERO));
            let message=chord_product(&q,abc);let m=transport().inverse(&message);
            for (i,&r) in active.iter().enumerate(){hm[i].push(m[r]);}
            let balance=(0..1024).filter(|&r|transport().inactive[r]).fold(K::ZERO,|s,r|s.add(m[r]));
            assert_eq!(balance,message[1023],"transport balancing coordinate");
            assert_eq!(balance,abc[1].mul(q[1021]).add(abc[2].mul(q[1022])),"source chord top coefficient");
            if degree<255{assert_eq!(balance,K::ZERO);}else{
                assert_eq!(balance,normal.mul(factor[255]));assert_ne!(balance,K::ZERO);
            }
            hm[214].push(balance);gm[274].push(balance);
            for i in 0..3{hm[215+i].push(dot(&point[i],&m));gm[271+i].push(dot(if i==0{&gp}else{&point[i]},&m));}
            for i in 0..271{gm[i].push(dot(&mix[i],&m));}
            let poly=aspis_core::sumcheck::polynomial_for_extension(&q,&gw);
            for (i,k) in [0,1,2,3,5,6].into_iter().enumerate(){gm[275+i].push(poly[k]);}
            for i in 0..1024{combined[i]=combined[i].add(q[i].mul(sample(6000+count)));}
            count+=1;
        }
        if degree<255{factor=super::final_posterior::times_x(&factor);}
    }
    assert_eq!(count,700);
    let (_,hp)=reduce(&hm);let (_,gg)=reduce(&gm);
    assert_eq!(hp.len(),218);assert_eq!(gg.len(),279);
    // Drop only the one special nonbalanced direction and the balance row.
    // The remaining basis has all three high quotient coordinates zero.
    let h_balanced:Vec<Vec<K>>=hm.iter().enumerate().filter(|(i,_)|*i!=214)
        .map(|(_,row)|row[..699].to_vec()).collect();
    let g_balanced:Vec<Vec<K>>=gm.iter().enumerate().filter(|(i,_)|*i!=274)
        .map(|(_,row)|row[..699].to_vec()).collect();
    let (_,hb)=reduce(&h_balanced);let (_,gb)=reduce(&g_balanced);
    assert_eq!(hb.len(),217);assert_eq!(gb.len(),278);
    let enc=CircleEncoder::new_for_domain_log(20);
    let qcode=enc.encode_c2_message(&combined).unwrap();
    let msg=chord_product(&combined,abc);let mcode=enc.encode_c2_message(&msg).unwrap();
    for &id in &p.queries{for s in 0..4{assert_eq!(qcode[4*id as usize+s],K::ZERO);assert_eq!(mcode[4*id as usize+s],K::ZERO);}}
    for pt in [p.p0,p.p1]{assert_eq!(eval_ood(&sparse(&msg),pt),K::ZERO);}
    assert!(fold_coefficients(&combined,p.alpha).iter().all(|&v|v==K::ZERO));
    println!("R17_FACTOR_KERNEL independent_directions=700 polynomial_factors_checked=234 H_residual_rank=218 G_residual_rank=279 source_raw_zeros=176 source_ood_zeros=2 prefix_only=true");
    println!("R17_BALANCED_KERNEL independent_directions=699 high_coordinates_zero=3 source_balance_identity_checked=700 H_residual_rank=217 G_residual_rank=278 prefix_only=true");
}

/// Constructive compatible raw/final interpolation. This deliberately does
/// NOT claim that the recovered original message is a legal H1 pad.
#[test]
#[ignore = "requires accepted R17 host public-prefix audit log"]
fn r17_actual_prefix_raw_final_interpolation() {
    use aspis_core::field::CM31;
    let (_, p) = super::final_posterior::read_public_prefix();
    let pts = selected_circle_fiber_points_shared(20, &p.queries).unwrap();
    let abc = [p.p0.x.mul(p.p1.y).sub(p.p0.y.mul(p.p1.x)),
        p.p0.y.sub(p.p1.y), p.p1.x.sub(p.p0.x)];
    let enc = CircleEncoder::new_for_domain_log(20);
    let mut original: Vec<_> = (0..1024).map(|i| sample(3000+i)).collect();
    original[1021] = abc[1].mul(sample(5000));
    original[1022] = abc[2].mul(sample(5000));
    original[1023] = K::ZERO;
    let raw = enc.encode_c2_message(&original).unwrap();
    let n = pts.len(); assert_eq!(n,22);
    for alpha in [p.alpha, K::ZERO, K::from_cm31(CM31::from_m31(pts[0].y.neg()))] {
        let finals = fold_coefficients(&original,alpha);
        let mut matrix=vec![vec![K::ZERO;n+3];n];
        for (i,pt) in pts.iter().enumerate() {
            let root=pt.x.mul(pt.x).double().sub(M31::ONE);
            for j in 0..n {
                let mut unit=vec![K::ZERO;256];unit[j]=K::ONE;
                matrix[i][j]=evaluate_final256_coefficients(&unit,root).unwrap();
            }
            let at=4*p.queries[i] as usize;
            let v=&raw[at..at+4];
            matrix[i][n]=v[0].sub(v[1]).sub(v[2]).add(v[3]).mul_m31(M31(4).mul(pt.y).inv());
            matrix[i][n+1]=v[0].add(v[1]).sub(v[2]).sub(v[3]).mul_m31(M31(4).mul(pt.x).inv());
            matrix[i][n+2]=v[0].sub(v[1]).add(v[2]).sub(v[3]).mul_m31(M31(4).mul(pt.x).mul(pt.y).inv());
            assert_eq!(qm31_circle_to_line_fold4(v.try_into().unwrap(),alpha,pt.x.double().inv(),pt.y.double().inv()),
                evaluate_final256_coefficients(&finals,root).unwrap());
        }
        let (rref,pivots)=reduce(&matrix);
        assert_eq!(pivots,(0..n).collect::<Vec<_>>());
        let mut q=vec![K::ZERO;1024];
        for i in 0..256 {
            let b=if i<n{rref[i][n]}else{K::ZERO};
            let c=if i<n{rref[i][n+1]}else{K::ZERO};
            let d=if i<n{rref[i][n+2]}else{K::ZERO};
            q[4*i]=finals[i].sub(alpha.mul(b)).sub(alpha.square().mul(c)).sub(alpha.pow(3).mul(d));
            q[4*i+1]=b;q[4*i+2]=c;q[4*i+3]=d;
        }
        assert_eq!(fold_coefficients(&q,alpha),finals);
        assert_eq!(&q[1021..],&[K::ZERO;3]);
        let repaired=enc.encode_c2_message(&q).unwrap();
        let message=chord_product(&q,abc);
        let original_message=transport().inverse(&message);
        assert!((0..N).any(|r|!transport().inactive[r] && original_message[r]!=K::ZERO),
            "negative control: raw/final interpolation alone must not be claimed as a legal H1 pad");
        let encoded_message=enc.encode_c2_message(&message).unwrap();
        for pt in [p.p0,p.p1]{assert_eq!(eval_ood(&sparse(&message),pt),K::ZERO);}
        for (i,pt) in pts.iter().enumerate(){for (s,(x,y)) in
            [(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)].into_iter().enumerate(){
            let at=4*p.queries[i] as usize+s;
            assert_eq!(repaired[at],raw[at]);
            let l=abc[0].add(abc[1].mul_m31(x)).add(abc[2].mul_m31(y));
            assert_eq!(encoded_message[at],l.mul(raw[at]));
        }}
    }
    println!("R17_RAW_FINAL_INTERPOLATION fibres=22 alpha_cases=3 raw_targets=88 final_targets=256 quotient_image_checked=true active_row_negative_control=true h1_legality_not_claimed=true");
}

#[test]
fn r17_two_channel_opening_arithmetic_and_public_tail() {
    use aspis_core::sumcheck::{boundary_sum, evaluate, polynomial_for_extension};
    let z = core::array::from_fn(|i| sample(i as u32 + 1));
    let p0 = secure_ood_circle_point_from_parameter(sample(71)).unwrap();
    let p1 = secure_ood_circle_point_from_parameter(sample(113)).unwrap();
    let abc = [
        p0.x.mul(p1.y).sub(p0.y.mul(p1.x)),
        p0.y.sub(p1.y),
        p1.x.sub(p0.x),
    ];
    let kappa = sample(191);
    let tau = sample(211);
    let originals = [
        original_weights(&z, kappa, false),
        original_weights(&z, kappa, true),
    ];
    let mut weights = [
        quotient_weights(&z, kappa, abc, tau, false),
        quotient_weights(&z, kappa, abc, tau, true),
    ];
    let mut q: [Vec<K>; 2] = core::array::from_fn(|channel| {
        let mut v: Vec<_> = (0..N)
            .map(|i| sample((i + channel * N + 1) as u32))
            .collect();
        v[1023] = K::ZERO;
        let t = sample((channel + 3300) as u32);
        v[1021] = abc[1].mul(t);
        v[1022] = abc[2].mul(t);
        v
    });
    let mut claim = K::ZERO;
    for channel in 0..2 {
        let mut interpolant = vec![K::ZERO; N];
        interpolant[0] = sample((channel + 3400) as u32);
        interpolant[if p0.x != p1.x { 2 } else { 1 }] = sample((channel + 3500) as u32);
        let lq = chord_product(&q[channel], abc);
        let encoded: Vec<_> = lq
            .iter()
            .zip(&interpolant)
            .map(|(&a, &b)| a.add(b))
            .collect();
        for point in [p0, p1] {
            assert_eq!(
                eval_ood(&sparse(&encoded), point),
                eval_ood(&sparse(&interpolant), point)
            );
        }
        let component_claim = dot(&originals[channel], &transport().inverse(&encoded))
            .sub(dot(&originals[channel], &transport().inverse(&interpolant)));
        let ordinary = chord_transpose(&transport().dual(&originals[channel]), abc);
        assert_eq!(component_claim, dot(&ordinary, &q[channel]));
        // Source image residuals vanish, but their relation-polynomial
        // contributions are retained in the full weight accumulator.
        assert_eq!(
            component_claim,
            boundary_sum(&polynomial_for_extension(&q[channel], &weights[channel]))
        );
        claim = claim.add(component_claim);
    }
    let first_parts: [_; 2] =
        core::array::from_fn(|i| polynomial_for_extension(&q[i], &weights[i]));
    let first = core::array::from_fn(|i| first_parts[0][i].add(first_parts[1][i]));
    assert_eq!(boundary_sum(&first), claim);
    assert_eq!(
        first[4],
        claim.mul_m31(M31_HALF).mul_m31(M31_HALF).sub(first[0])
    );
    let alpha = sample(151);
    claim = evaluate(&first, alpha);
    let mut public_finals = [
        fold_coefficients(&q[0], alpha),
        fold_coefficients(&q[1], alpha),
    ];
    for w in &mut weights {
        w.fold_deferred_relation_arity4(alpha);
    }
    let mut queries = vec![4, 6];
    queries.extend((0..20).map(|i| 1000 + 7919 * i));
    let pts = selected_circle_fiber_points_shared(20, &queries).unwrap();
    let enc = CircleEncoder::new_for_domain_log(20);
    let xs: Vec<_> = pts
        .iter()
        .map(|p| p.x.mul(p.x).double().sub(M31::ONE))
        .collect();
    let mut raw_folded = [Vec::new(), Vec::new()];
    for channel in 0..2 {
        for (i, pt) in pts.iter().enumerate() {
            let raw = core::array::from_fn(|slot| {
                (0..N).fold(K::ZERO, |s, j| {
                    s.add(
                        q[channel][j].mul_m31(
                            enc.encode_c1_basis_value(j, 4 * queries[i] as usize + slot)
                                .unwrap(),
                        ),
                    )
                })
            });
            let v = qm31_circle_to_line_fold4(raw, alpha, pt.x.double().inv(), pt.y.double().inv());
            assert_eq!(
                v,
                evaluate_final256_coefficients(&public_finals[channel], xs[i]).unwrap()
            );
            raw_folded[channel].push(v);
        }
    }
    // This prototype's proposed injection uses disjoint rho powers, not
    // the same 22 powers twice (which would permit cross-channel cancellation).
    let rho = sample(251);
    let mut power = rho;
    for channel in 0..2 {
        let scales: Vec<_> = (0..22)
            .map(|_| {
                let s = power;
                power = power.mul(rho);
                s
            })
            .collect();
        weights[channel].add_line_m31_batch(&scales, &xs).unwrap();
        claim = claim.add(dot(&scales, &raw_folded[channel]));
    }
    // Discard the unpublished quotient preimages. All subsequent relation
    // messages use only the public Final512, public weights/openings, and
    // later challenges. This is a prototype dataflow, not source replay.
    q[0].clear();
    q[1].clear();
    for round in 1..4 {
        let parts: [_; 2] =
            core::array::from_fn(|i| polynomial_for_extension(&public_finals[i], &weights[i]));
        let polynomial = core::array::from_fn(|i| parts[0][i].add(parts[1][i]));
        assert_eq!(boundary_sum(&polynomial), claim);
        assert_eq!(
            polynomial[4],
            claim.mul_m31(M31_HALF).mul_m31(M31_HALF).sub(polynomial[0])
        );
        let a = sample(151 + round);
        claim = evaluate(&polynomial, a);
        for channel in 0..2 {
            weights[channel].fold_deferred_relation_arity4(a);
            public_finals[channel] = fold_coefficients(&public_finals[channel], a);
        }
    }
    let terminal = (0..2).fold(K::ZERO, |s, channel| {
        s.add(
            public_finals[channel]
                .iter()
                .enumerate()
                .fold(K::ZERO, |s, (i, &v)| {
                    s.add(v.mul(weights[channel].weight_at(i as u32)))
                }),
        )
    });
    assert_eq!(claim, terminal);
    println!("R17_TWO_CHANNEL_ARITHMETIC interpolants=2 image_gates=4 final_values=512 raw_checks=44 injection_powers=44 relation_rounds=4 public_tail=true");
}
