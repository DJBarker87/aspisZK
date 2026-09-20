// Included only in the staged research payment module. Internal map is
// never serialized; this opt-in diagnostic does not sample an oracle.
fn r17_h1_semantic_audit(
    p: &impl PaymentInput,
    tr: &PoolV1PairLatePublicStatementV1,
    m: &[Vec<K>],
    s: &row::Semantic,
) {
    let gc = crate::structured_g::mixed_coins(&m[27]);
    let coefficient = |z: &[K; 10]| {
        let rows = point_rows_with_g(m, z, &gc);
        let mut claims: [K; 84] = core::array::from_fn(|i| rows[(i / 28) * 29 + i % 28]);
        claims[26] = K::ZERO;
        let zero = payment_terminal(p, tr, &claims, z, s);
        claims[26] = K::ONE;
        let one = payment_terminal(p, tr, &claims, z, s);
        claims[26] = sc(2);
        let two = payment_terminal(p, tr, &claims, z, s);
        let delta = one.sub(zero);
        assert_eq!(
            two.sub(zero),
            delta.add(delta),
            "source helper affine control"
        );
        delta
    };
    // The same literal interpolation used by the semantic producer.
    let interpolation: Vec<[K; 28]> = (0..28)
        .map(|x| {
            let mut unit = [K::ZERO; 28];
            unit[x] = K::ONE;
            interpolate_degree27(&unit)
        })
        .collect();
    let mut coordinates = vec![vec![K::ZERO; 1024]; 271];
    let mut carry = vec![K::ZERO; 1024];
    for r in 0..10 {
        let left = 9 - r;
        let prefix: Vec<K> = (0..1usize << r)
            .map(|bits| {
                (0..r).fold(K::ONE, |a, j| {
                    a.mul(if bits >> (r - 1 - j) & 1 == 1 {
                        s.z[j]
                    } else {
                        K::ONE.sub(s.z[j])
                    })
                })
            })
            .collect();
        let mut samples = vec![vec![K::ZERO; 1024]; 28];
        for x in 0..28 {
            let xk = sc(x as u32);
            let mut z = s.z;
            z[r] = xk;
            for assignment in 0..1usize << left {
                for j in 0..left {
                    z[r + 1 + j] = sc(((assignment >> (left - 1 - j)) & 1) as u32);
                }
                let c = coefficient(&z);
                // A Boolean suffix fixes all suffix row bits, avoiding a
                // dense 1024-entry MLE expansion at every sample point.
                for (bits, &a) in prefix.iter().enumerate() {
                    let base = (bits << (left + 1)) | assignment;
                    let v = c.mul(a);
                    samples[x][base] = samples[x][base].add(v.mul(K::ONE.sub(xk)));
                    samples[x][base | (1 << left)] = samples[x][base | (1 << left)].add(v.mul(xk));
                }
            }
        }
        if r == 0 {
            for j in 0..1024 {
                carry[j] = samples[0][j].add(samples[1][j]);
                coordinates[0][j] = carry[j];
            }
        }
        for j in 0..1024 {
            let poly: [K; 28] = core::array::from_fn(|k| {
                (0..28).fold(K::ZERO, |a, x| {
                    a.add(interpolation[x][k].mul(samples[x][j]))
                })
            });
            assert_eq!(
                state_only_boundary_sum(&poly),
                carry[j],
                "H1 source boundary r={r} j={j}"
            );
            coordinates[1 + 27 * r][j] = poly[0].sub(carry[j].half());
            for k in 2..28 {
                coordinates[1 + 27 * r + k - 1][j] = poly[k];
            }
            carry[j] = evaluate_state_only_polynomial(&poly, s.z[r]);
        }
    }
    let terminal = coefficient(&s.z);
    for j in 0..1024 {
        let mle = (0..10).fold(K::ONE, |a, bit| {
            a.mul(if j >> (9 - bit) & 1 == 1 {
                s.z[bit]
            } else {
                K::ONE.sub(s.z[bit])
            })
        });
        let coins: [K; 271] = core::array::from_fn(|i| coordinates[i][j]);
        assert_eq!(carry[j], terminal.mul(mle), "H1 source terminal basis {j}");
        assert_eq!(
            crate::structured_g::mask_eval(&coins, &s.z),
            carry[j],
            "normalized H1 coordinates {j}"
        );
    }
    let map = crate::r16_basis_transport::transport();
    let pivot = (0..1024).find(|&i| map.inactive[i]).unwrap();
    let mut legal = 0;
    for j in 0..1024 {
        if map.inactive[j] && j != pivot {
            let mut pad = vec![K::ZERO; 1024];
            pad[j] = K::ONE;
            pad[pivot] = K::ONE.neg();
            let mut h = vec![K::ZERO; 1024];
            apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut h, &pad).unwrap();
            assert_eq!(h, pad);
            assert_eq!(
                coordinates[0][j], coordinates[0][pivot],
                "legal H1 initial contribution"
            );
            legal += 1;
        }
    }
    assert_eq!(legal, 809);
    println!("R17_H1_SEMANTIC_MAP coordinates=271 columns=1024 rounds=10 terminal_basis_checks=1024 legal_initial_directions=809 internal_map_not_serialized=true");
}
