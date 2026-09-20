// In-process, fixed-prefix correction witness. Nothing private is exported.
mod r17_coupled_audit {
    use super::*;
    pub(super) fn dot(a: &[K], b: &[K]) -> K {
        assert_eq!(a.len(), b.len());
        a.iter().zip(b).fold(K::ZERO, |s, (&a, &b)| s.add(a.mul(b)))
    }
    fn xt(v: &[K]) -> Vec<K> {
        let mut out = vec![K::ZERO; v.len() + 1];
        for (j, &value) in v.iter().enumerate() {
            let (mut row, mut bit, mut scale) = (j, 0, M31::ONE);
            while row & (1 << bit) != 0 {
                row ^= 1 << bit;
                scale = scale.mul(corelib::field::M31_HALF);
                out[row] = out[row].add(value.mul_m31(scale));
                bit += 1;
            }
            out[row | (1 << bit)] = out[row | (1 << bit)].add(value.mul_m31(scale));
        }
        out
    }
    pub(super) fn chord(q: &[K], [a, b, c]: [K; 3]) -> Vec<K> {
        let e: Vec<_> = q.chunks_exact(2).map(|v| v[0]).collect();
        let o: Vec<_> = q.chunks_exact(2).map(|v| v[1]).collect();
        let xe = xt(&e);
        let xo = xt(&o);
        let xxo = xt(&xo);
        let get = |v: &[K], i| v.get(i).copied().unwrap_or(K::ZERO);
        let mut out = vec![K::ZERO; 1028];
        for i in 0..514 {
            out[2 * i] = a
                .mul(get(&e, i))
                .add(b.mul(get(&xe, i)))
                .add(c.mul(get(&o, i).sub(get(&xxo, i))));
            out[2 * i + 1] = c
                .mul(get(&e, i))
                .add(a.mul(get(&o, i)))
                .add(b.mul(get(&xo, i)));
        }
        assert!(out[1024..].iter().all(|&v| v == K::ZERO));
        out.truncate(1024);
        out
    }
    pub(super) fn qvector(x: &[K], abc: [K; 3]) -> Vec<K> {
        let mut q = x[..1021].to_vec();
        q.extend([abc[1].mul(x[1021]), abc[2].mul(x[1021]), K::ZERO]);
        q
    }
    pub(super) fn eval_weights(x: K, y: K) -> Vec<K> {
        let mut factors = [K::ZERO; 10];
        factors[0] = y;
        factors[1] = x;
        for i in 2..10 {
            factors[i] = factors[i - 1].square().mul_m31(M31(2)).sub(K::ONE);
        }
        (0..1024)
            .map(|j| {
                (0..10)
                    .filter(|&i| j & (1 << i) != 0)
                    .fold(K::ONE, |a, i| a.mul(factors[i]))
            })
            .collect()
    }
    pub(super) fn reduce(a: &mut [Vec<K>], columns: usize) -> Vec<usize> {
        let mut pivots = vec![];
        for col in 0..columns {
            let r = pivots.len();
            let Some(p) = (r..a.len()).find(|&i| a[i][col] != K::ZERO) else {
                continue;
            };
            a.swap(r, p);
            let inv = a[r][col].inv();
            for v in &mut a[r][col..] {
                *v = v.mul(inv);
            }
            let row = a[r].clone();
            for i in 0..a.len() {
                if i == r {
                    continue;
                }
                let f = a[i][col];
                if f == K::ZERO {
                    continue;
                }
                for j in col..row.len() {
                    a[i][j] = a[i][j].sub(f.mul(row[j]));
                }
            }
            pivots.push(col);
            if pivots.len() == a.len() {
                break;
            }
        }
        pivots
    }
    pub(super) fn run(
        hmap: &[Vec<K>],
        z: &[K; 10],
        p: &Prefix,
        kappa: K,
        alpha: K,
        queries: &[u32],
        verify_source_raw: impl Fn(&[K]),
    ) {
        let map = crate::r16_basis_transport::transport();
        let pts = corelib::circle_fri::selected_circle_fiber_points_shared(20, queries).unwrap();
        let raw: Vec<Vec<K>> = pts
            .iter()
            .flat_map(|pt| {
                [
                    (pt.x, pt.y),
                    (pt.x, pt.y.neg()),
                    (pt.x.neg(), pt.y.neg()),
                    (pt.x.neg(), pt.y),
                ]
            })
            .map(|(x, y)| {
                eval_weights(
                    K::from_cm31(CM31::from_m31(x)),
                    K::from_cm31(CM31::from_m31(y)),
                )
            })
            .collect();
        let point: Vec<Vec<K>> = corelib::v6_transcript::v6_statement_points(z)
            .iter()
            .map(|z| {
                let mut w = WeightAccumulator::empty(10);
                w.add_multilinear(K::ONE, z.to_vec()).unwrap();
                (0..1024).map(|i| w.weight_at(i)).collect()
            })
            .collect();
        let ood: Vec<_> = p.points.iter().map(|p| eval_weights(p.x, p.y)).collect();
        let active: Vec<_> = (0..1024).filter(|&i| !map.inactive[i]).collect();
        assert_eq!(active.len(), 214);
        let mut hmatrix = vec![vec![K::ZERO; 1022]; 562];
        let mut gmatrix = vec![vec![K::ZERO; 1022]; 625];
        let gw = crate::opening_weights::quotient_weights(z, kappa, p.abc, p.tau, true);
        let hw = crate::opening_weights::quotient_weights(z, kappa, p.abc, p.tau, false);
        let mixing: Vec<_> = (0..271).map(crate::structured_g::mixing_row).collect();
        let gpoint = crate::structured_g::mask_weights(z);
        for col in 0..1022 {
            let mut unit = vec![K::ZERO; 1022];
            unit[col] = K::ONE;
            let q = qvector(&unit, p.abc);
            let c = chord(&q, p.abc);
            let m = map.inverse(&c);
            for w in &ood {
                assert_eq!(dot(w, &c), K::ZERO);
            }
            let cs: Vec<_> = c
                .iter()
                .enumerate()
                .filter(|(_, v)| **v != K::ZERO)
                .map(|(i, &v)| (i, v))
                .collect();
            let ms: Vec<_> = m
                .iter()
                .enumerate()
                .filter(|(_, v)| **v != K::ZERO)
                .map(|(i, &v)| (i, v))
                .collect();
            let mdot = |w: &[K]| ms.iter().fold(K::ZERO, |s, &(i, v)| s.add(w[i].mul(v)));
            for (i, &r) in active.iter().enumerate() {
                hmatrix[i][col] = m[r];
            }
            let balance = m
                .iter()
                .enumerate()
                .filter(|(i, _)| map.inactive[*i])
                .fold(K::ZERO, |s, (_, &v)| s.add(v));
            hmatrix[214][col] = balance;
            gmatrix[618][col] = balance;
            for i in 0..88 {
                let v = cs
                    .iter()
                    .fold(K::ZERO, |s, &(j, v)| s.add(raw[i][j].mul(v)));
                hmatrix[215 + i][col] = v;
                gmatrix[271 + i][col] = v;
            }
            for i in 0..3 {
                hmatrix[303 + i][col] = mdot(&point[i]);
                gmatrix[359 + i][col] = mdot(if i == 0 { &gpoint } else { &point[i] });
            }
            let finals = primal(&q, alpha);
            for i in 0..256 {
                hmatrix[306 + i][col] = finals[i];
                gmatrix[362 + i][col] = finals[i];
            }
            for i in 0..271 {
                gmatrix[i][col] = mdot(&mixing[i]);
            }
            let poly = corelib::sumcheck::polynomial_for_extension(&q, &gw);
            for (i, j) in [0, 1, 2, 3, 5, 6].into_iter().enumerate() {
                gmatrix[619 + i][col] = poly[j];
            }
        }
        let mut hr = hmatrix.clone();
        let hp = reduce(&mut hr, 1022);
        assert_eq!(hp.len(), 540);
        let free = (0..1022).find(|i| !hp.contains(i)).unwrap();
        let mut hx = vec![K::ZERO; 1022];
        hx[free] = K::ONE;
        for (i, &j) in hp.iter().enumerate() {
            hx[j] = hr[i][free].neg();
        }
        for row in &hmatrix {
            assert_eq!(dot(row, &hx), K::ZERO);
        }
        let hq = qvector(&hx, p.abc);
        let hm = map.inverse(&chord(&hq, p.abc));
        let mut applied = vec![K::ZERO; 1024];
        apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut applied, &hm).unwrap();
        assert_eq!(applied, hm);
        let hcoins: Vec<_> = hmap.iter().map(|r| dot(r, &hm)).collect();
        assert!(
            hcoins.iter().any(|&v| v != K::ZERO),
            "nontrivial semantic correction"
        );
        assert_eq!(hcoins[0], K::ZERO);
        let hpoly = corelib::sumcheck::polynomial_for_extension(&hq, &hw);
        assert_eq!(corelib::sumcheck::boundary_sum(&hpoly), K::ZERO);
        assert_eq!(corelib::sumcheck::evaluate(&hpoly, alpha), K::ZERO);
        let mut target = vec![K::ZERO; 625];
        for i in 0..271 {
            target[i] = hcoins[i].neg();
        }
        let ratio = p.gamma.inv(); // gamma^26 / gamma^27, not an omitted normalization.
        for (i, j) in [0, 1, 2, 3, 5, 6].into_iter().enumerate() {
            target[619 + i] = hpoly[j].mul(ratio).neg();
        }
        let mut gr = gmatrix.clone();
        for (i, row) in gr.iter_mut().enumerate() {
            row.push(target[i]);
        }
        let gp = reduce(&mut gr, 1022);
        assert_eq!(gp.len(), 601);
        assert!(
            gr[601..].iter().all(|r| r[1022] == K::ZERO),
            "incompatible coupled correction"
        );
        let mut gx = vec![K::ZERO; 1022];
        for (i, &j) in gp.iter().enumerate() {
            gx[j] = gr[i][1022];
        }
        for (i, row) in gmatrix.iter().enumerate() {
            assert_eq!(dot(row, &gx), target[i], "original matrix row {i}");
        }
        let gq = qvector(&gx, p.abc);
        let gm = map.inverse(&chord(&gq, p.abc));
        let gcoins = crate::structured_g::mixed_coins(&gm);
        for i in 0..271 {
            assert_eq!(gcoins[i].add(hcoins[i]), K::ZERO);
        }
        let gpoly = corelib::sumcheck::polynomial_for_extension(&gq, &gw);
        for i in 0..7 {
            assert_eq!(
                hpoly[i]
                    .mul(p.gamma.pow(26))
                    .add(gpoly[i].mul(p.gamma.pow(27))),
                K::ZERO
            );
        }
        for m in [&hm, &gm] {
            verify_source_raw(m);
            for point in p.points {
                assert_eq!(super::ood(m, point), K::ZERO);
            }
        }
        for point in corelib::v6_transcript::v6_statement_points(z) {
            assert_eq!(multilinear_evaluate_qm31(&hm, &point).unwrap(), K::ZERO);
        }
        for point in corelib::v6_transcript::v6_statement_points(z)
            .iter()
            .skip(1)
        {
            assert_eq!(multilinear_evaluate_qm31(&gm, point).unwrap(), K::ZERO);
        }
        assert_eq!(crate::structured_g::mask_eval(&gcoins, z), K::ZERO);
        println!("R17_COUPLED_CORRECTION source_H1_map=true H1_observations_zero=347 G_observations_zero=348 semantic_coordinates_cancel=271 relation_coefficients_cancel=7 gamma_normalization=true selected_encoder_zeros=176 source_ood_zeros=4 internal_vectors_not_serialized=true");
    }
}
