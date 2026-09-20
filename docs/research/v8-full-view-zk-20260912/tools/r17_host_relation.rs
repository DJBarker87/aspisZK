//! Isolated R17 host profile. No production/deployment adapter or privacy claim.
use super::inactive_binding as row;
use super::*;

pub(super) struct Prepared {
    pub(super) public_audit: [K; 11],
    pub(super) p: Prefix,
    pub(super) iv_g: [K; 2],
    pub(super) weights: [WeightAccumulator; 2],
    pub(super) claim: K,
}

pub(super) fn initial(old: K, g: &[K]) -> K {
    let old_g = g.iter().enumerate().fold(K::ZERO, |s, (r, &v)| {
        let z = core::array::from_fn(|bit| sc(((r >> (9 - bit)) & 1) as u32));
        s.add(v.mul(corelib::state_only_hiding::state_only_explicit_g_mask_factor(&z)))
    });
    old.sub(old_g).add(structured_g::mixed_coins(g)[0])
}

pub(super) fn prepare(s: row::Semantic, w: &Wire<'_>) -> Result<Prepared, Error> {
    let (mut t, points, gamma) = row::to_gamma(s.t, w)?;
    t.absorb(label::V6_INACTIVE_CLAIM, &bytes(&w.v[358..359]));
    let kappa = sample(&mut t, true)?;
    let scales = [kappa, kappa.square(), kappa.pow(3)];
    let gp = gamma.pow(27);
    let batch = |v: &[K]| v.iter().rev().fold(K::ZERO, |a, v| a.mul(gamma).add(*v));
    let mut claim = w.v[358];
    for r in 0..3 {
        claim = claim.add(scales[r].mul(batch(&w.v[271 + 29 * r..300 + 29 * r])));
    }
    let [p0, p1] = points;
    let use_x = p0.x != p1.x;
    let h0 = if use_x { p0.x } else { p0.y };
    let h1 = if use_x { p1.x } else { p1.y };
    let inv = h0.sub(h1).try_inv().ok_or(Error::Domain)?;
    let all = [batch(&w.v[359..388]), batch(&w.v[388..417])];
    let gv = [gp.mul(w.v[359 + 27]), gp.mul(w.v[388 + 27])];
    let rv = [all[0].sub(gv[0]), all[1].sub(gv[1])];
    let line = |v: [K; 2]| {
        let slope = v[0].sub(v[1]).mul(inv);
        [v[0].sub(slope.mul(h0)), slope]
    };
    let iv = line(rv);
    let iv_g = line(gv);
    let abc = [
        p0.x.mul(p1.y).sub(p0.y.mul(p1.x)),
        p0.y.sub(p1.y),
        p1.x.sub(p0.x),
    ];
    let mut ordinary = [Vec::new(), Vec::new()];
    for channel in 0..2 {
        let original = opening_weights::original_weights(&s.z, kappa, channel == 1);
        let dual = basis_transport::transport().dual(&original);
        let i = if channel == 0 { iv } else { iv_g };
        claim = claim
            .sub(i[0].mul(dual[0]))
            .sub(i[1].mul(dual[if use_x { 2 } else { 1 }]));
        ordinary[channel] = opening_weights::chord_transpose(&dual, abc);
    }
    let mut descriptor = b"AV8/R17/Vandermonde1024-nodes1to1024/271-coins/two-channel/v1".to_vec();
    let map = basis_transport::transport();
    for &r in &map.order {
        descriptor.extend((r as u16).to_le_bytes());
    }
    for &i in &map.inactive {
        descriptor.push(i as u8);
    }
    t.absorb(label::PROFILE, &descriptor);
    for (channel, v) in ordinary.iter().enumerate() {
        t.absorb(label::PROFILE, &[channel as u8]);
        t.absorb(label::PROFILE, &bytes(v));
    }
    t.absorb(label::CLAIM, &bytes(&[claim]));
    t.absorb(label::PROFILE, b"AV8/R17/four-image-residuals/v1");
    let tau = sample(&mut t, true)?;
    let weights = core::array::from_fn(|channel| {
        let mut v = ordinary[channel].clone();
        let a = if channel == 0 { tau } else { tau.pow(3) };
        let b = if channel == 0 {
            tau.square()
        } else {
            tau.pow(4)
        };
        v[1023] = v[1023].add(a);
        v[1022] = v[1022].add(b.mul(abc[1]));
        v[1021] = v[1021].sub(b.mul(abc[2]));
        let mut weights = WeightAccumulator::empty(10);
        weights.add_dense(v).unwrap();
        weights
    });
    Ok(Prepared {
        public_audit: core::array::from_fn(|i| if i < 10 { s.z[i] } else { kappa }),
        p: Prefix {
            t,
            points,
            gamma,
            abc,
            iv,
            use_x,
            tau,
        },
        iv_g,
        weights,
        claim,
    })
}

pub(super) fn opened(
    w: &Wire<'_>,
    p: &Prefix,
    iv_g: [K; 2],
    queries: &[u32],
    alpha: K,
) -> Result<([Vec<K>; 2], Vec<M31>), Error> {
    let pts = corelib::circle_fri::selected_circle_fiber_points_shared(20, queries)
        .map_err(|_| Error::Domain)?;
    let powers = StateOnlySpendQueryPowers::new(p.gamma);
    let gp = p.gamma.pow(27);
    let mut entries = Vec::new();
    let mut values = [Vec::new(), Vec::new()];
    let mut xs = Vec::new();
    for (i, base) in pts.iter().enumerate() {
        let r = &w.records[i * REC..(i + 1) * REC];
        let salt: &[u8; 32] = r[589..621].try_into().unwrap();
        // This selected decoder validates ALL C1/C2 limbs before the G view
        // is read by the otherwise non-validating packed accessor below.
        let all = gamma_combine_v6_packed_layer0(&r[..403], &r[403..589], &powers)
            .map_err(|_| Error::Canonical)?;
        let gv: [K; 4] = core::array::from_fn(|slot| {
            gp.mul(corelib::v6_onefold::packed_qm31_at(&r[403..589], 4 + slot).unwrap())
        });
        entries.push((
            queries[i],
            private_leaf_hash_v7(hash, V7_C1_TREE_TAG, &r[..403], salt),
            private_leaf_hash_v7(hash, V7_C2_TREE_TAG, &r[403..589], salt),
        ));
        if base.x == M31::ZERO || base.y == M31::ZERO {
            return Err(Error::Domain);
        }
        for channel in 0..2 {
            let mut q = [K::ZERO; 4];
            let iv = if channel == 0 { p.iv } else { iv_g };
            for (slot, (x, y)) in [
                (base.x, base.y),
                (base.x, base.y.neg()),
                (base.x.neg(), base.y.neg()),
                (base.x.neg(), base.y),
            ]
            .into_iter()
            .enumerate()
            {
                let v = if channel == 0 {
                    all[slot].sub(gv[slot])
                } else {
                    gv[slot]
                };
                let denom = p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y));
                q[slot] = v
                    .sub(iv[0].add(iv[1].mul_m31(if p.use_x { x } else { y })))
                    .mul(denom.try_inv().ok_or(Error::Domain)?);
            }
            values[channel].push(corelib::field::qm31_circle_to_line_fold4(
                q,
                alpha,
                base.x.double().inv(),
                base.y.double().inv(),
            ));
        }
        xs.push(base.x.mul(base.x).double().sub(M31::ONE));
    }
    entries.sort_by_key(|e| e.0);
    if !verify_two_minimal_subtrees_v7_bytes(
        hash,
        (&w.roots.0, &w.roots.1),
        18,
        &entries,
        w.frontiers,
        &mut vec![],
        &mut vec![],
    ) {
        return Err(Error::Authentication);
    }
    // Retain an independently implemented original combined-opening check.
    let old = Prefix {
        t: p.t.clone(),
        points: p.points,
        gamma: p.gamma,
        abc: p.abc,
        iv: [p.iv[0].add(iv_g[0]), p.iv[1].add(iv_g[1])],
        use_x: p.use_x,
        tau: p.tau,
    };
    let (reference, reference_xs) = opened_values_reference(w, &old, queries, alpha, hash)?;
    if reference_xs != xs
        || reference
            .iter()
            .enumerate()
            .any(|(i, &v)| v != values[0][i].add(values[1][i]))
    {
        return Err(Error::Terminal);
    }
    Ok((values, xs))
}

pub(super) fn polynomial(q: &[Vec<K>; 2], weights: &[WeightAccumulator; 2]) -> [K; 7] {
    let a = polynomial_for_extension(&q[0], &weights[0]);
    let b = polynomial_for_extension(&q[1], &weights[1]);
    core::array::from_fn(|i| a[i].add(b[i]))
}

pub(super) fn inject_two(
    weights: &mut [WeightAccumulator; 2],
    claim: &mut K,
    values: &[Vec<K>; 2],
    xs: &[M31],
    rho: K,
) -> Result<K, Error> {
    let mut power = rho;
    let mut total = K::ZERO;
    for channel in 0..2 {
        let scales: Vec<_> = (0..Q)
            .map(|_| {
                let v = power;
                power = power.mul(rho);
                v
            })
            .collect();
        weights[channel]
            .add_line_m31_batch(&scales, xs)
            .map_err(|_| Error::Shape)?;
        total = total.add(dot(&scales, &values[channel]));
    }
    *claim = claim.add(total);
    Ok(total)
}

fn fold_dense(v: &[K], a: K) -> Vec<K> {
    v.chunks_exact(4)
        .map(|v| {
            v[0].add(a.mul(v[3].add(a.mul(v[2].add(a.mul(v[1]))))))
                .half()
                .half()
        })
        .collect()
}

pub(super) fn verify(w: &Wire<'_>, prepared: Prepared, reference: bool) -> Result<(), Error> {
    let Prepared {
        public_audit,
        mut p,
        iv_g,
        mut weights,
        mut claim,
    } = prepared;
    let mut dense: [Vec<K>; 2] =
        core::array::from_fn(|c| (0..1024).map(|i| weights[c].weight_at(i)).collect());
    let first = compact(&w.v[417..423], claim);
    absorb_round(&mut p.t, 0, &first);
    let mut work = vec![0];
    work.extend_from_slice(&w.nonces[8..16]);
    p.t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE, &work);
    let a = sample(&mut p.t, false)?;
    claim = evaluate(&first, a);
    for c in 0..2 {
        if reference {
            dense[c] = fold_dense(&dense[c], a);
        } else {
            weights[c].fold_deferred_relation_arity4(a);
        }
    }
    let mut finals = [w.v[441..697].to_vec(), w.v[697..953].to_vec()];
    let (queries, rho) = query_schedule(&mut p, &w.v[441..953], w.nonces)?;
    let (values, xs) = opened(w, &p, iv_g, &queries, a)?;
    let inc = if reference {
        let mut power = rho;
        let mut inc = K::ZERO;
        for c in 0..2 {
            for i in 0..Q {
                inc = inc.add(power.mul(values[c][i]));
                for j in 0..256 {
                    let mut unit = vec![K::ZERO; 256];
                    unit[j] = K::ONE;
                    dense[c][j] = dense[c][j].add(
                        power.mul(
                            corelib::v6_onefold::evaluate_final256_coefficients(&unit, xs[i])
                                .map_err(|_| Error::Shape)?,
                        ),
                    );
                }
                power = power.mul(rho);
            }
        }
        claim = claim.add(inc);
        inc
    } else {
        inject_two(&mut weights, &mut claim, &values, &xs, rho)?
    };
    p.t.absorb(label::PROFILE, &bytes(&[inc]));
    for r in 1..4 {
        let poly = compact(&w.v[417 + 6 * r..423 + 6 * r], claim);
        absorb_round(&mut p.t, r, &poly);
        let a = sample(&mut p.t, false)?;
        claim = evaluate(&poly, a);
        for c in 0..2 {
            finals[c] = primal(&finals[c], a);
            if reference {
                dense[c] = fold_dense(&dense[c], a);
            } else {
                weights[c].fold_deferred_relation_arity4(a);
            }
        }
    }
    let terminal = (0..2).fold(K::ZERO, |s, c| {
        s.add((0..4).fold(K::ZERO, |s, i| {
            s.add(finals[c][i].mul(if reference {
                dense[c][i]
            } else {
                weights[c].weight_at(i as u32)
            }))
        }))
    });
    if terminal != claim {
        return Err(Error::Terminal);
    }
    // Read-only diagnostic of an accepted public proof. No witness, mask,
    // seed or additional oracle query is involved. Never emitted normally.
    if !reference && std::env::args().nth(1).as_deref() == Some("--audit-existing") {
        let mut fields = public_audit.to_vec();
        fields.extend([
            p.tau,
            a,
            p.points[0].x,
            p.points[0].y,
            p.points[1].x,
            p.points[1].y,
            p.gamma,
        ]);
        eprintln!(
            "R17_PUBLIC_PREFIX {{\"fields\":{:?},\"queries\":{:?}}}",
            bytes(&fields),
            queries
        );
    }
    Ok(())
}
