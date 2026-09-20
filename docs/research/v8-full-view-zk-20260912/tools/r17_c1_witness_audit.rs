// Fixed-prefix C1 witness-offset correction, not a complete transcript coupling.
fn r17_h1_witness_joint_audit(
    h0: &[K], c1: &[Vec<M31>], z: &[K; 10], p: &Prefix,
    alpha: K, queries: &[u32], enc: &CircleEncoder, decoder: &ac::Decoder,
) -> (Vec<K>, Vec<K>) {
    use r17_coupled_audit::{chord, dot, eval_weights, qvector, reduce};
    let map = crate::r16_basis_transport::transport();
    let scale = p.gamma.pow(26);
    assert_ne!(scale, K::ZERO);
    let mut rest: Vec<_> = h0.iter().map(|&h| h.mul(scale)).collect();
    for c in 0..16 { for r in 0..1024 {
        rest[r] = rest[r].add(p.gamma.pow(c as u64).mul_m31(c1[c][r]));
    }}
    for pt in p.points { assert_eq!(ood(&rest, pt), K::ZERO); }
    let encoded = enc.encode_c2_message(&map.forward(&rest)).unwrap();
    let fibers = corelib::circle_fri::selected_circle_fiber_points_shared(20, &(0..256).collect::<Vec<u32>>()).unwrap();
    let mut values = Vec::new();
    for (i, pt) in fibers.iter().enumerate() {
        for (s, (x,y)) in [(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)].into_iter().enumerate() {
            let l = p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y));
            values.push(encoded[4*i+s].mul(l.try_inv().unwrap()));
        }
    }
    let rq = decoder.solve_wide(&values);
    assert_eq!(rq[1023], K::ZERO);
    assert_eq!(p.abc[1].mul(rq[1022]), p.abc[2].mul(rq[1021]));
    assert_eq!(chord(&rq, p.abc), map.forward(&rest));
    let finals = primal(&rq, alpha);
    let rawpoints = corelib::circle_fri::selected_circle_fiber_points_shared(20, queries).unwrap();
    let raw: Vec<_> = rawpoints.iter().flat_map(|pt| [(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)])
        .map(|(x,y)| eval_weights(K::from_cm31(CM31::from_m31(x)), K::from_cm31(CM31::from_m31(y)))).collect();
    let point: Vec<Vec<K>> = corelib::v6_transcript::v6_statement_points(z).iter().map(|z| {
        let mut w = WeightAccumulator::empty(10); w.add_multilinear(K::ONE,z.to_vec()).unwrap();
        (0..1024).map(|i| w.weight_at(i)).collect()
    }).collect();
    let active: Vec<_> = (0..1024).filter(|&r| !map.inactive[r]).collect();
    assert_eq!(active.len(),214);
    let mut matrix = vec![vec![K::ZERO;1022];562];
    for j in 0..1022 {
        let mut unit=vec![K::ZERO;1022];unit[j]=K::ONE;
        let q=qvector(&unit,p.abc);let c=chord(&q,p.abc);let m=map.inverse(&c);
        for (i,&r) in active.iter().enumerate(){matrix[i][j]=m[r];}
        matrix[214][j]=(0..1024).filter(|&r|map.inactive[r]).fold(K::ZERO,|s,r|s.add(m[r]));
        for i in 0..88{matrix[215+i][j]=dot(&raw[i],&c);}
        for i in 0..3{matrix[303+i][j]=dot(&point[i],&m);}
        let f=primal(&q,alpha);for i in 0..256{matrix[306+i][j]=f[i];}
    }
    let hc=map.forward(h0);let mut target=vec![K::ZERO;562];
    for i in 0..88{target[215+i]=dot(&raw[i],&hc).neg();}
    for i in 0..3{target[303+i]=dot(&point[i],h0).neg();}
    for i in 0..256{target[306+i]=finals[i].mul(scale.inv()).neg();}
    let mut reduced=matrix.clone();for i in 0..562{reduced[i].push(target[i]);}
    let pivots=reduce(&mut reduced,1022);assert_eq!(pivots.len(),540);
    assert!(reduced[540..].iter().all(|r|r[1022]==K::ZERO),"affine H1 joint compatibility");
    let mut x=vec![K::ZERO;1022];for (i,&j) in pivots.iter().enumerate(){x[j]=reduced[i][1022];}
    for i in 0..562{assert_eq!(dot(&matrix[i],&x),target[i]);}
    let q=qvector(&x,p.abc);let pad=map.inverse(&chord(&q,p.abc));
    let mut applied=vec![K::ZERO;1024];apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut applied,&pad).unwrap();assert_eq!(applied,pad);
    let h:Vec<_>=h0.iter().zip(&pad).map(|(&a,&b)|a.add(b)).collect();
    let code=enc.encode_c2_message(&map.forward(&h)).unwrap();
    for &id in queries{for s in 0..4{assert_eq!(code[4*id as usize+s],K::ZERO);}}
    for w in &point{assert_eq!(dot(w,&h),K::ZERO);}
    for pt in corelib::v6_transcript::v6_statement_points(z){assert_eq!(multilinear_evaluate_qm31(&h,&pt).unwrap(),K::ZERO);}
    for pt in p.points{assert_eq!(ood(&h,pt),K::ZERO);}
    let total:Vec<_>=rq.iter().zip(&q).map(|(&a,&b)|a.add(scale.mul(b))).collect();
    assert!(primal(&total,alpha).iter().all(|&v|v==K::ZERO));
    println!("R17_H1_WITNESS_JOINT rank=540 equations=562 compatibility_residuals=22 raw_zero=88 point_zero=3 ood_zero=2 rest_final_zero=256 gamma26_retained=true fixed_prefix_only=true");
    (h, total)
}

// Literal old/new terminal enumeration, including nonlinear C1 interactions.
fn r17_witness_semantic_delta(p: &impl PaymentInput, tr: &PoolV1PairLatePublicStatementV1,
    old: &[Vec<K>], new: &[Vec<K>], s: &row::Semantic) -> [K;271] {
    let og=crate::structured_g::mixed_coins(&old[27]);
    let ng=crate::structured_g::mixed_coins(&new[27]);
    let zero=[K::ZERO;271];
    let gd: [K;271]=core::array::from_fn(|i|ng[i].sub(og[i]));
    // Remove G at all three point claims, not just its structured first
    // point. The non-G path now receives no old/new G data at all.
    let mut old_without_g=old.to_vec();old_without_g[27].fill(K::ZERO);
    let mut new_without_g=new.to_vec();new_without_g[27].fill(K::ZERO);
    let mut coords=[K::ZERO;271];let mut carry=K::ZERO;
    for r in 0..10 {
        let left=9-r;let mut samples=[K::ZERO;28];
        for x in 0..28 {let mut z=s.z;z[r]=sc(x as u32);
            for assignment in 0..1usize<<left {
                for j in 0..left {z[r+1+j]=sc(((assignment>>(left-1-j))&1)as u32);}
                let literal=terminal_with_g(p,tr,new,&z,s,&ng).sub(terminal_with_g(p,tr,old,&z,s,&og));
                let without_g=terminal_with_g(p,tr,&new_without_g,&z,s,&zero).sub(terminal_with_g(p,tr,&old_without_g,&z,s,&zero));
                let split=without_g.add(crate::structured_g::mask_eval(&gd,&z));
                assert_eq!(literal,split,"source G independence r={r} x={x}");
                samples[x]=samples[x].add(split);
            }
        }
        let poly=interpolate_degree27(&samples);
        if r==0 {carry=state_only_boundary_sum(&poly);coords[0]=carry;}
        assert_eq!(state_only_boundary_sum(&poly),carry,"witness semantic boundary {r}");
        coords[1+27*r]=poly[0].sub(carry.half());
        for k in 2..28 {coords[1+27*r+k-1]=poly[k];}
        carry=evaluate_state_only_polynomial(&poly,s.z[r]);
    }
    assert_eq!(carry,terminal_with_g(p,tr,new,&s.z,s,&ng).sub(terminal_with_g(p,tr,old,&s.z,s,&og)));
    assert_eq!(crate::structured_g::mask_eval(&coords,&s.z),carry);
    coords
}

fn r17_g_witness_audit(delta: &[K;271], rq: &[K], z: &[K;10], p: &Prefix,
    kappa: K, alpha: K, queries: &[u32], enc: &CircleEncoder) -> Vec<K> {
    use r17_coupled_audit::{chord,dot,eval_weights,qvector,reduce};
    let map=crate::r16_basis_transport::transport();
    let gw=crate::opening_weights::quotient_weights(z,kappa,p.abc,p.tau,true);
    let rw=crate::opening_weights::quotient_weights(z,kappa,p.abc,p.tau,false);
    let rp=corelib::sumcheck::polynomial_for_extension(rq,&rw);
    assert_eq!(corelib::sumcheck::boundary_sum(&rp),K::ZERO);
    assert_eq!(corelib::sumcheck::evaluate(&rp,alpha),K::ZERO);
    // The C1 witness correction changes the initial mask claim. Coordinate
    // zero is an affine target for G, not a precondition that it is zero.
    assert_eq!(crate::structured_g::mask_eval(delta,z),K::ZERO,"retained terminal");
    let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,queries).unwrap();
    let raw:Vec<_>=pts.iter().flat_map(|p|[(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)])
        .map(|(x,y)|eval_weights(K::from_cm31(CM31::from_m31(x)),K::from_cm31(CM31::from_m31(y)))).collect();
    let mut point:Vec<Vec<K>>=corelib::v6_transcript::v6_statement_points(z).iter().map(|z|{
        let mut w=WeightAccumulator::empty(10);w.add_multilinear(K::ONE,z.to_vec()).unwrap();
        (0..1024).map(|i|w.weight_at(i)).collect()
    }).collect();point[0]=crate::structured_g::mask_weights(z);
    let mixing:Vec<_>=(0..271).map(crate::structured_g::mixing_row).collect();
    let mut matrix=vec![vec![K::ZERO;1022];625];
    for j in 0..1022 {
        let mut unit=vec![K::ZERO;1022];unit[j]=K::ONE;
        let q=qvector(&unit,p.abc);let c=chord(&q,p.abc);let m=map.inverse(&c);
        for i in 0..271{matrix[i][j]=dot(&mixing[i],&m);}
        for i in 0..88{matrix[271+i][j]=dot(&raw[i],&c);}
        for i in 0..3{matrix[359+i][j]=dot(&point[i],&m);}
        let f=primal(&q,alpha);for i in 0..256{matrix[362+i][j]=f[i];}
        matrix[618][j]=(0..1024).filter(|&r|map.inactive[r]).fold(K::ZERO,|s,r|s.add(m[r]));
        let poly=corelib::sumcheck::polynomial_for_extension(&q,&gw);
        for (i,k) in [0,1,2,3,5,6].into_iter().enumerate(){matrix[619+i][j]=poly[k];}
    }
    let mut target=vec![K::ZERO;625];for i in 0..271{target[i]=delta[i].neg();}
    let scale=p.gamma.pow(27);assert_ne!(scale,K::ZERO);
    for (i,k) in [0,1,2,3,5,6].into_iter().enumerate(){target[619+i]=rp[k].mul(scale.inv()).neg();}
    let mut reduced=matrix.clone();for i in 0..625{reduced[i].push(target[i]);}
    let pivots=reduce(&mut reduced,1022);assert_eq!(pivots.len(),601);
    assert!(reduced[601..].iter().all(|r|r[1022]==K::ZERO),"affine G witness compatibility");
    let mut x=vec![K::ZERO;1022];for (i,&j) in pivots.iter().enumerate(){x[j]=reduced[i][1022];}
    for i in 0..625{assert_eq!(dot(&matrix[i],&x),target[i],"original G row {i}");}
    let q=qvector(&x,p.abc);let g=map.inverse(&chord(&q,p.abc));
    let gc=crate::structured_g::mixed_coins(&g);
    for i in 0..271{assert_eq!(gc[i].add(delta[i]),K::ZERO);}
    let gp=corelib::sumcheck::polynomial_for_extension(&q,&gw);
    for i in 0..7{assert_eq!(rp[i].add(scale.mul(gp[i])),K::ZERO);}
    let code=enc.encode_c2_message(&map.forward(&g)).unwrap();
    for &id in queries{for s in 0..4{assert_eq!(code[4*id as usize+s],K::ZERO);}}
    for pt in p.points{assert_eq!(ood(&g,pt),K::ZERO);}
    for pt in corelib::v6_transcript::v6_statement_points(z).iter().skip(1){assert_eq!(multilinear_evaluate_qm31(&g,pt).unwrap(),K::ZERO);}
    assert_eq!(crate::structured_g::mask_eval(&gc,z),K::ZERO);
    assert!(primal(&q,alpha).iter().all(|&v|v==K::ZERO));
    println!("R17_G_WITNESS_JOINT equations=625 rank=601 compatibility_residuals=24 semantic_cancel=271 relation_cancel=7 raw_zero=88 point_zero=3 ood_zero=2 final_zero=256 fixed_prefix_only=true");
    g
}

// First affine helper step only: retain both OOD values with a legal pad.
// Raw, point, final and semantic observations still require joint correction.
fn r17_h1_witness_ood_audit(before: &[K], after: &[K], points: [Point; 2]) -> Vec<K> {
    assert_eq!(before.len(), 1024);
    assert_eq!(after.len(), 1024);
    let map = crate::r16_basis_transport::transport();
    let base: Vec<_> = after.iter().zip(before).map(|(&a, &b)| a.sub(b)).collect();
    let rows: Vec<_> = (0..1023).filter(|&r| map.inactive[r]).collect();
    assert_eq!(rows.len(), 809);
    assert!(map.inactive[1023]);
    let mut matrix = vec![vec![K::ZERO; rows.len()]; 2];
    for (j, &r) in rows.iter().enumerate() {
        let mut unit = vec![K::ZERO; 1024];
        unit[r] = K::ONE;
        unit[1023] = K::ONE.neg();
        for i in 0..2 { matrix[i][j] = ood(&unit, points[i]); }
    }
    let target = [ood(&base, points[0]).neg(), ood(&base, points[1]).neg()];
    let mut reduced = matrix.clone();
    for i in 0..2 { reduced[i].push(target[i]); }
    let pivots = r17_coupled_audit::reduce(&mut reduced, rows.len());
    assert_eq!(pivots.len(), 2, "actual helper OOD correction rank");
    let mut x = vec![K::ZERO; rows.len()];
    for (i, &j) in pivots.iter().enumerate() { x[j] = reduced[i][rows.len()]; }
    for i in 0..2 {
        assert_eq!(matrix[i].iter().zip(&x).fold(K::ZERO, |s, (&a, &b)| s.add(a.mul(b))), target[i]);
    }
    let mut pad = vec![K::ZERO; 1024];
    for (j, &r) in rows.iter().enumerate() {
        pad[r] = x[j];
        pad[1023] = pad[1023].sub(x[j]);
    }
    let mut applied = vec![K::ZERO; 1024];
    apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut applied, &pad).unwrap();
    assert_eq!(applied, pad);
    let result: Vec<_> = base.iter().zip(&pad).map(|(&a, &b)| a.add(b)).collect();
    for i in 0..2 { assert_eq!(ood(&result, points[i]), K::ZERO); }
    for r in 0..1024 { if !map.inactive[r] { assert_eq!(result[r], base[r]); } }
    println!("R17_H1_WITNESS_OOD rank=2 legal_directions=809 source_pad_checked=true retained_ood=2 active_helper_offset_retained=true fixed_prefix_only=true");
    result
}

fn r17_c1_witness_audit(
    base: &[Vec<M31>],
    z: &[K; 10],
    points: [Point; 2],
    queries: &[u32],
    enc: &CircleEncoder,
) -> Vec<Vec<M31>> {
    let map = crate::r16_basis_transport::transport();
    let mut index = vec![0; 1024];
    for (j, &r) in map.order.iter().enumerate() {
        index[r] = j;
    }
    let cells = pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
    // The selected mask application overwrites the last legal inactive
    // cell with minus the other inactive cells. A compiler-trace difference
    // must undergo that same balancing before comparing equal mask coins.
    let mut balanced = base.to_vec();
    for col in 0..16 {
        let dependent = cells
            .iter()
            .filter(|c| c.column as usize == col && map.inactive[c.row as usize])
            .last()
            .unwrap()
            .row as usize;
        assert_eq!(dependent, 1023);
        balanced[col][dependent] = (0..1024)
            .filter(|&r| map.inactive[r] && r != dependent)
            .fold(M31::ZERO, |a, r| a.add(base[col][r]))
            .neg();
    }
    let base = balanced.as_slice();
    let point_weights: Vec<Vec<K>> = corelib::v6_transcript::v6_statement_points(z)
        .iter()
        .map(|p| {
            let mut w = WeightAccumulator::empty(10);
            w.add_multilinear(K::ONE, p.to_vec()).unwrap();
            (0..1024).map(|i| w.weight_at(i)).collect()
        })
        .collect();
    let ood_weights: Vec<Vec<K>> = points
        .iter()
        .map(|p| {
            let mut f = [K::ZERO; 10];
            f[0] = p.y;
            f[1] = p.x;
            for i in 2..10 {
                f[i] = f[i - 1].square().mul_m31(M31(2)).sub(K::ONE);
            }
            (0..1024)
                .map(|j| {
                    (0..10)
                        .filter(|&i| j & (1 << i) != 0)
                        .fold(K::ONE, |a, i| a.mul(f[i]))
                })
                .collect()
        })
        .collect();
    let raw: Vec<Vec<M31>> = queries
        .iter()
        .flat_map(|&q| (0..4).map(move |s| 4 * q as usize + s))
        .map(|pos| {
            (0..1024)
                .map(|j| enc.encode_c1_basis_value(j, pos).unwrap())
                .collect()
        })
        .collect();
    let limbs = |v: K| [v.c0.a, v.c0.b, v.c1.a, v.c1.b];
    let dot = |a: &[M31], b: &[M31]| {
        a.iter()
            .zip(b)
            .fold(M31::ZERO, |s, (&a, &b)| s.add(a.mul(b)))
    };
    let qdot = |a: &[K], b: &[M31]| {
        a.iter()
            .zip(b)
            .fold(K::ZERO, |s, (&a, &b)| s.add(a.mul_m31(b)))
    };
    let mut result = base.to_vec();
    let mut changed = 0;
    for col in 0..16 {
        changed += base[col].iter().filter(|&&v| v != M31::ZERO).count();
        let rows: Vec<_> = cells
            .iter()
            .filter(|c| c.column as usize == col && c.row != 1023 && !(col == 3 && c.row == 1014))
            .map(|c| c.row as usize)
            .collect();
        let width = rows.len();
        let mut matrix = vec![vec![M31::ZERO; width]; 108];
        for (k, &r) in rows.iter().enumerate() {
            let j = index[r];
            for i in 0..88 {
                matrix[i][k] = raw[i][j];
            }
            for (i, w) in point_weights.iter().enumerate() {
                let v = if map.inactive[r] {
                    w[r].sub(w[1023])
                } else {
                    w[r]
                };
                for (b, v) in limbs(v).into_iter().enumerate() {
                    matrix[88 + 4 * i + b][k] = v;
                }
            }
            for (i, w) in ood_weights.iter().enumerate() {
                for (b, v) in limbs(w[j]).into_iter().enumerate() {
                    matrix[100 + 4 * i + b][k] = v;
                }
            }
            let mut unit = vec![M31::ZERO; 1024];
            unit[r] = M31::ONE;
            if map.inactive[r] {
                unit[1023] = M31::ONE.neg();
            }
            let transformed = map.forward(&unit);
            assert_eq!(transformed[j], M31::ONE);
            assert_eq!(transformed.iter().filter(|&&v| v != M31::ZERO).count(), 1);
        }
        let encoded = map.forward(&base[col]);
        let mut target = vec![M31::ZERO; 108];
        for i in 0..88 {
            target[i] = dot(&raw[i], &encoded).neg();
        }
        for (i, w) in point_weights.iter().enumerate() {
            for (b, v) in limbs(qdot(w, &base[col])).into_iter().enumerate() {
                target[88 + 4 * i + b] = v.neg();
            }
        }
        for (i, w) in ood_weights.iter().enumerate() {
            for (b, v) in limbs(qdot(w, &encoded)).into_iter().enumerate() {
                target[100 + 4 * i + b] = v.neg();
            }
        }
        let mut reduced = matrix.clone();
        for (i, row) in reduced.iter_mut().enumerate() {
            row.push(target[i]);
        }
        let mut pivots = vec![];
        for k in 0..width {
            let rank = pivots.len();
            let Some(p) = (rank..108).find(|&r| reduced[r][k] != M31::ZERO) else {
                continue;
            };
            reduced.swap(rank, p);
            let inv = reduced[rank][k].inv();
            for v in &mut reduced[rank][k..] {
                *v = v.mul(inv);
            }
            let pivot = reduced[rank].clone();
            for r in 0..108 {
                if r == rank {
                    continue;
                }
                let f = reduced[r][k];
                if f == M31::ZERO {
                    continue;
                }
                for j in k..=width {
                    reduced[r][j] = reduced[r][j].sub(f.mul(pivot[j]));
                }
            }
            pivots.push(k);
            if pivots.len() == 108 {
                break;
            }
        }
        assert_eq!(
            pivots.len(),
            108,
            "C1 actual-prefix correction rank col={col}"
        );
        let mut solution = vec![M31::ZERO; width];
        for (r, &k) in pivots.iter().enumerate() {
            solution[k] = reduced[r][width];
        }
        for i in 0..108 {
            assert_eq!(dot(&matrix[i], &solution), target[i]);
        }
        for (k, &r) in rows.iter().enumerate() {
            result[col][r] = result[col][r].add(solution[k]);
            if map.inactive[r] {
                result[col][1023] = result[col][1023].sub(solution[k]);
            }
        }
        let codeword = enc.encode_c1_message(&map.forward(&result[col])).unwrap();
        for &q in queries {
            for slot in 0..4 {
                assert_eq!(codeword[4 * q as usize + slot], M31::ZERO);
            }
        }
        let wide: Vec<_> = result[col]
            .iter()
            .map(|&v| K::from_cm31(CM31::from_m31(v)))
            .collect();
        for p in corelib::v6_transcript::v6_statement_points(z) {
            assert_eq!(multilinear_evaluate_qm31(&wide, &p).unwrap(), K::ZERO);
        }
        for p in points {
            assert_eq!(ood(&wide, p), K::ZERO);
        }
        assert_eq!(
            result[col]
                .iter()
                .enumerate()
                .filter(|(i, _)| map.inactive[*i])
                .fold(M31::ZERO, |a, (_, &v)| a.add(v)),
            M31::ZERO
        );
    }
    assert!(changed > 0, "genuine witness offset required");
    println!("R17_C1_WITNESS_CORRECTION columns=16 rank_per_column=108 selected_raw_zeros=1408 point_claim_zeros=48 ood_claim_zeros=32 changed_witness_cells={changed} base_field_masks=true internal_vectors_not_serialized=true");
    result
}
