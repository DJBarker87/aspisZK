// Fixed-prefix C1 witness-offset correction, not a complete transcript coupling.
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
