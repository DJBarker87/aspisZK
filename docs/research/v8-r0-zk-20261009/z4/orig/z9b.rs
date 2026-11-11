//! Z9b (LOG D30.6 lane D): on the real R1 payload of Z9,
//!  (1) relR1 exactly as written in t2b2b/DESIGN-R1-PRIVACY-MODEL.txt §2.4
//!      (RoundPairing quarter conventions; lineFoldLayer/lineFoldValue of
//!      V5ComponentCConcreteFoldLinearity; secondLinear of R1/RepeatedLift with
//!      storedLine16X; exactFinalLinear with storedFirstLineX18), checked as an
//!      annihilator of bat(ker own), with the lineInverse table in three readings;
//!  (2) C1Lift_c (c < 16) and H1Lift of §3.3, each on its own, opened part and
//!      the 24 remaining limbs separately;
//!  (3) BCondG_R1 (B0R1 <= V_G) and the fallback B0own <= V_G.
//! A child module of z9 (reuses its private R1 port). Exact arithmetic.
use super::*;
use aspis_core::r0::{encoder, opening};

fn rev(width: usize, x: usize) -> usize {
    (0..width).fold(0, |acc, b| acc | (((x >> b) & 1) << (width - 1 - b)))
}
/// X(g^e), g = (2, 1268011823) (CircleGroupOrder.lean:176).
fn gx(e: u64) -> M31 {
    CM31::new(M31(2), M31(1268011823)).pow(e).a
}
/// storedFirstLineX18 (V7ExactOneFoldDomains.lean:348): X(g^(2048 + 8192 rev18 p)).
fn x18(p: usize) -> M31 {
    gx(2048 + 8192 * rev(18, p) as u64)
}
/// storedLine16X (V5FriReleasedLineGeometry.lean:64): X(g^(8192 + 32768 rev16 v)).
fn x16(v: usize) -> M31 {
    gx(8192 + 32768 * rev(16, v) as u64)
}
fn t2(x: M31) -> M31 {
    x.mul(x).double().sub(M31::ONE)
}
/// naturalLinePoly j evaluated at x: prod over set bits b of T_{2^b}(x).
fn nat_line(x: M31, j: usize) -> M31 {
    let mut out = M31::ONE;
    let mut t = x;
    let mut j = j;
    while j > 0 {
        if j & 1 == 1 {
            out = out.mul(t);
        }
        t = t2(t);
        j >>= 1;
    }
    out
}
fn wm(x: M31) -> W {
    W::from_m31(x)
}
/// lineFoldValue / pairFoldValue (V5ComponentCConcreteFoldLinearity.lean:110-120).
fn pair_fold(c: W, inv: W, l: W, r: W) -> W {
    let half = W::from_m31(M31(2).inv());
    l.add(r).mul(half).add(c.mul(l.sub(r).mul(inv)))
}
fn line_fold_value(alpha: W, inv: [W; 3], v: [W; 4]) -> W {
    pair_fold(alpha.mul(alpha), inv[2], pair_fold(alpha, inv[0], v[0], v[1]), pair_fold(alpha, inv[1], v[2], v[3]))
}
/// RoundPairing.dualFold: quarter * sum_t w(4d+t) alpha^((4-t)%4).
fn rp_dual_fold(alpha: W, w: &[W]) -> Vec<W> {
    let quarter = W::from_m31(M31(4).inv());
    w.chunks_exact(4)
        .map(|h| quarter.mul((0..4).fold(W::ZERO, |s, t| s.add(h[t].mul(alpha.pow(((4 - t) % 4) as u64))))))
        .collect()
}
const READINGS: [&str; 3] = ["inv_xyz_literal", "inv_2x_m2y_2z", "inv_2x_2y_2z"];
fn line_inverse(v: usize, reading: usize) -> [W; 3] {
    let x = x18(4 * v);
    let y = x18(4 * v + 3);
    let z = t2(x);
    let two = M31(2);
    match reading {
        0 => [wm(x.inv()), wm(y.inv()), wm(z.inv())],
        1 => [wm(two.mul(x).inv()), W::ZERO.sub(wm(two.mul(y).inv())), wm(two.mul(z).inv())],
        _ => [wm(two.mul(x).inv()), wm(two.mul(y).inv()), wm(two.mul(z).inv())],
    }
}
/// weightsR1 (§2.3) through the R0 Lean-mirror functions: indicator of copy-inactive
/// rows at pi.symm j, eqWeight(openingPoints) at pi.symm j, libraWeight j, oodLinear.
fn weights_design(a: &[QM31; 10], z: &[Point<QM31>; 2], kappa: W) -> Vec<W> {
    let pts = opening::points_from_alphas(&a.map(wq));
    let rw: Vec<_> = (0..3).map(|k| opening::row_eq_weight(&pts[k])).collect();
    let kp = r1::powers::<7>(kappa);
    (0..1024)
        .map(|j| {
            let r = r1::row(j);
            let mut e = [QM31::ZERO; 1024];
            e[j] = QM31::ONE;
            let ell = [
                if opening::inactive(r).unwrap() { W::ONE } else { W::ZERO },
                rw[0][r],
                rw[1][r],
                rw[2][r],
                wq(h_weight(a, j)),
                wq(encoder::eval_message(&e, z[0])),
                wq(encoder::eval_message(&e, z[1])),
            ];
            (0..7).fold(W::ZERO, |s, k| s.add(kp[k].mul(ell[k])))
        })
        .collect()
}
struct DesignRels {
    s2a: Rel,
    s2b: Rel,
    s1: Rel,
    circ: Vec<Rel>,
    line: Vec<Vec<Rel>>, // per reading, one relation per distinct parent u/4
}
fn design_relations(wd: &[W], op: &Opening, qs: &[usize], lay: &Lay) -> DesignRels {
    let quarter = W::from_m31(M31(4).inv());
    let w1 = rp_dual_fold(op.alpha0, wd);
    let w2 = rp_dual_fold(op.alpha1, &w1);
    let neg = |x: W| W::ZERO.sub(x);
    let mut s2b = vec![(8, W::ONE), (12, W::ONE)];
    for i in 0..7 {
        s2b.push((1 + i, neg(quarter.mul(op.alpha0.pow(i as u64)))));
    }
    let mut s1: Vec<(usize, W)> = (0..7).map(|i| (8 + i, op.alpha1.pow(i as u64))).collect();
    for e in 0..64 {
        s1.push((lay.fin(e), neg(w2[e])));
    }
    let mut parents: Vec<usize> = qs.iter().map(|u| u / 4).collect();
    parents.sort();
    parents.dedup();
    let line = (0..3)
        .map(|rd| {
            parents
                .iter()
                .map(|&v| {
                    let inv = line_inverse(v, rd);
                    let mut c = vec![];
                    for t in 0..4 {
                        let mut unit = [W::ZERO; 4];
                        unit[t] = W::ONE;
                        c.push((lay.fw(4 * v + t), line_fold_value(op.alpha1, inv, unit)));
                    }
                    let xv = x16(v);
                    for e in 0..64 {
                        c.push((lay.fin(e), neg(wm(nat_line(xv, e)))));
                    }
                    Rel { name: format!("line_v{v}_{}", READINGS[rd]), c }
                })
                .collect()
        })
        .collect();
    DesignRels {
        s2a: Rel { name: "s2a".into(), c: vec![(1, W::ONE), (5, W::ONE)] },
        s2b: Rel { name: "s2b".into(), c: s2b },
        s1: Rel { name: "s1".into(), c: s1 },
        circ: qs.iter().map(|&u| Rel { name: format!("circ_u{u}"), c: vec![(lay.fw(u), W::ONE)] }).collect(),
        line,
    }
}

/// Z10's canonic-coset point index i in [0, 2^20) (point GEN^(1024 + 2048 i)) -> R1 fibre u.
fn z10_fibre(i: u64) -> usize {
    let m: u64 = 1 << 31;
    let e = (1024 + 2048 * i) % m;
    for c in [e, (m - e) % m, (e + (1 << 30)) % m, (m - e + (1 << 30)) % m] {
        if c >= 1024 && (c - 1024) % 4096 == 0 && (c - 1024) / 4096 < (1 << 18) {
            return rev(18, ((c - 1024) / 4096) as usize);
        }
    }
    panic!("no fibre for z10 index {i}");
}
fn query_set(spec: &str, trial_qs: &[usize]) -> Vec<usize> {
    let (kind, seed) = spec.split_once(':').unwrap_or((spec, "0"));
    let seed: u64 = seed.parse().unwrap();
    let mut rng = Rng(0x5a39_b0b0_2026_1018u64.wrapping_add((seed + 1).wrapping_mul(0x9e3779b97f4a7c15)));
    let mut out: Vec<usize> = vec![];
    match kind {
        "actual" => out = trial_qs.to_vec(),
        "consecutive0" => out = (0..22).collect(),
        "spaced" => out = (0..22).map(|i| i * 8192).collect(),
        "paired" => out = (0..11).flat_map(|i| [i, i + (1 << 17)]).collect(),
        "random" => {
            while out.len() < 22 {
                let n = (rng.next() % (1 << 18)) as usize;
                if !out.contains(&n) {
                    out.push(n);
                }
            }
        }
        "consecutive" | "coset" => {
            let i0 = rng.next() % (1 << 20);
            let mut k = 0u64;
            while out.len() < 22 {
                let i = if kind == "coset" { (i0 + k * (1 << 14)) % (1 << 20) } else { (i0 + k) % (1 << 20) };
                k += 1;
                let u = z10_fibre(i);
                if !out.contains(&u) {
                    out.push(u);
                }
            }
        }
        _ => panic!("unknown query set {spec}"),
    }
    out.sort_unstable();
    out
}

fn fmt_groups(v: &[(String, Vec<Vec<M31>>)]) -> String {
    v.iter().map(|(n, f)| format!("{n}:{}", f.len())).collect::<Vec<_>>().join(",")
}

/// C1Lift / H1Lift ranks for one lane. Sources carry the 112 (F lane) or 376 (H1) own
/// limbs: claims(0..12) extra(12..16) ood(16..24) opened(24..). Returns
/// (rank obs(V), rank obs(W), opened rank on V, opened rank on W, rest rank on V0, rest rank on W0).
fn lift_ranks(width: usize, v_src: &[Vec<M31>], w_src: &[Vec<M31>]) -> [usize; 6] {
    let full = |s: &[Vec<M31>]| rank_of(width, s.iter().cloned());
    let opened = |s: &[Vec<M31>]| rank_of(width - 24, s.iter().map(|x| x[24..].to_vec()));
    let rest0 = |s: &[Vec<M31>]| {
        let mut ker = vec![];
        lane_elim(s.len(), |i| (s[i][24..].to_vec(), s[i][..24].to_vec()), |c| ker.push(c));
        rank_of(24, ker.into_iter())
    };
    [full(v_src), full(w_src), opened(v_src), opened(w_src), rest0(v_src), rest0(w_src)]
}

pub(crate) fn main() {
    let args: Vec<_> = std::env::args().collect();
    let get = |k: &str| args.windows(2).find(|x| x[0] == k).map(|x| x[1].clone());
    let s = get("--structure").expect("--structure");
    let v: usize = get("--vector").expect("--vector").parse().unwrap();
    let qspec = get("--qset").unwrap_or("actual".into());
    let start = Instant::now();
    let pi = d18_transport();
    z5::set_transport(pi);
    let t = trial(v);
    let a = alpha_for(&s, v, &t.a);
    let qs = query_set(&qspec, &t.qs);
    let label = format!("structure={s} vector={v} qset={qspec}");
    let lay = Lay::new(&qs);
    let nparents = lay.nf / 4;
    println!("Z9B_START {label} queries={qs:?} distinct_parents={nparents} folded_values={} batched_E={} lambda_dims={:?}", lay.nf, lay.nb, lambda_dims(&a));
    let (br, gr) = raw_c(&a, &t.z, &qs);
    let geo = Geo::new();
    // Geometry: Lean stored domains against the Rust domain used by the Z9 port.
    let mut geo_bad = [0usize; 3];
    for &p in &lay.fpos {
        if x18(p) != geo.levels[0][p] {
            geo_bad[0] += 1;
        }
        for d in 0..256 {
            if nat_line(x18(p), d) != geo.unit_eval(d, p) {
                geo_bad[1] += 1;
            }
        }
    }
    for &u in &qs {
        let b = final_basis(u);
        let xv = x16(u / 4);
        if (0..64).any(|e| nat_line(xv, e) != b[e]) {
            geo_bad[2] += 1;
        }
    }
    println!("Z9B_GEOMETRY {label} x18_vs_rust_levels0_mismatch={} natural_eval_vs_rust_mismatch={} x16_basis_vs_rust_accumulate_mismatch={}", geo_bad[0], geo_bad[1], geo_bad[2]);

    // (2) C1Lift_c and H1Lift (independent of gamma, kappa, alpha0, alpha1).
    assert!(inactive(1023) && inactive(0), "balance rows 1023 (eligible noise) and 0 (H1 padding) are copy-inactive");
    let mut c1_fail = vec![];
    for c in 0..16 {
        let vrows: Vec<usize> = (0..N).filter(|&r| r != 1023 && eligible(c, r)).collect();
        let bal = |r: usize| -> Vec<M31> {
            if inactive(r) {
                sub_vec(&br[r][1..], &br[1023][1..], |x, y| x.sub(y))
            } else {
                br[r][1..].to_vec()
            }
        };
        let vs: Vec<Vec<M31>> = vrows.iter().map(|&r| bal(r)).collect();
        let ws: Vec<Vec<M31>> = (0..N).filter(|&r| r != 1023).map(|r| bal(r)).collect();
        let rk = lift_ranks(112, &vs, &ws);
        let ok = rk[0] == rk[1];
        if !ok {
            c1_fail.push(c);
        }
        println!(
            "Z9B_C1LIFT {label} lane={c} eligible_sources={} rank_obs_V={} rank_obs_W={} opened_V={} opened_W={} rest_on_ker_opened_V={} rest_on_ker_opened_W={} c1lift={ok}",
            vs.len(), rk[0], rk[1], rk[2], rk[3], rk[4], rk[5]
        );
    }
    {
        let x = |k: usize| tower(k);
        let bal = |r: usize, k: usize| -> Vec<M31> {
            if inactive(r) {
                flatten(&scale(&sub_vec(&gr[r][1..], &gr[0][1..], |p, q| p.sub(q)), x(k)))
            } else {
                flatten(&scale(&gr[r][1..], x(k)))
            }
        };
        let ps: Vec<Vec<M31>> = (1..N).filter(|&r| inactive(r)).flat_map(|r| (0..4).map(move |k| (r, k))).map(|(r, k)| bal(r, k)).collect();
        let ws: Vec<Vec<M31>> = (1..N).flat_map(|r| (0..4).map(move |k| (r, k))).map(|(r, k)| bal(r, k)).collect();
        let rk = lift_ranks(376, &ps, &ws);
        println!(
            "Z9B_H1LIFT {label} padding_sources={} rank_obs_P={} rank_obs_W={} opened_P={} opened_W={} rest_on_ker_opened_P={} rest_on_ker_opened_W={} h1lift={}",
            ps.len(), rk[0], rk[1], rk[2], rk[3], rk[4], rk[5], rk[0] == rk[1]
        );
        println!("Z9B_LIFTS {label} c1lift_all={} c1lift_failing_lanes={c1_fail:?} h1lift={}", c1_fail.is_empty(), rk[0] == rk[1]);
    }
    println!("Z9B_LIFTS_DONE {label} seconds={:.3}", start.elapsed().as_secs_f64());

    // (1) and (3) per gamma limb set.
    for gi in 0..2 {
        let glabel = format!("{label} gamma={gi}");
        let op = opening_challenges(v, gi);
        let zk = [[t.z[0].x, t.z[0].y], [t.z[1].x, t.z[1].y]];
        let wts = r1::Weights::new(&a, &zk);
        let w = wts.materialize(op.kappa, inactive_fn);
        let wd = weights_design(&a, &t.z, op.kappa);
        let weights_equal = w == wd;
        let phi = unit_functionals(&geo, &w, &op, &lay);
        let beta: Vec<Vec<W>> = (0..N).map(|r| phi[usize::from(pi[r])].clone()).collect();
        let gpow = (0..29).map(|l| op.gamma.pow(l as u64)).collect();
        let tail: Vec<_> = (0..N).map(|r| tail_row(&a, r)).collect();
        let cx = Ctx { a, br: br.clone(), gr: gr.clone(), tail, beta, gpow, lay: Lay::new(&qs) };
        let lay = &cx.lay;
        let bw = lay.bw;
        // Rust line_fold equals lineFoldValue under reading 1 on unit vectors.
        let mut rust_vs_reading = [0usize; 3];
        for &u in &qs {
            for rd in 0..3 {
                for tt in 0..4 {
                    let mut unit = [W::ZERO; 4];
                    unit[tt] = W::ONE;
                    if line_fold(op.alpha1, u / 4, unit) != line_fold_value(op.alpha1, line_inverse(u / 4, rd), unit) {
                        rust_vs_reading[rd] += 1;
                    }
                }
            }
        }
        let dr = design_relations(&wd, &op, &qs, lay);
        let mut groups: Vec<(String, Vec<Vec<M31>>)> = vec![
            ("ia".into(), Rel { name: "ia".into(), c: vec![(0, W::ONE)] }.limb_functionals(bw)),
            ("s2a".into(), dr.s2a.limb_functionals(bw)),
            ("s2b".into(), dr.s2b.limb_functionals(bw)),
            ("s1".into(), dr.s1.limb_functionals(bw)),
            ("circ".into(), dr.circ.iter().flat_map(|r| r.limb_functionals(bw)).collect()),
        ];
        for rd in 0..3 {
            groups.push((format!("line[{}]", READINGS[rd]), dr.line[rd].iter().flat_map(|r| r.limb_functionals(bw)).collect()));
        }
        println!(
            "Z9B_DESIGN {glabel} weightsR1_equals_rust_materialize={weights_equal} rust_line_fold_mismatch_per_reading={rust_vs_reading:?} relations_written=3+{}circ+{}line distinct_parents={nparents} groups=[{}]",
            dr.circ.len(), dr.line[0].len(), fmt_groups(&groups)
        );
        let ln = Lanes::new(&cx);
        // Pass 1 (batched carry only): bat(ker own).
        let mut b0own = Ech::new(bw);
        for li in 0..LANES {
            lane_elim(ln.count(li), |i| { let (o, b, _) = ln.bal(li, i); (o, wflat(&b)) }, |c| { b0own.insert(c); });
        }
        let ia_piv = (0..8).filter(|&i| b0own.p[i].is_some()).count();
        let un = explain(&glabel, "design_relR1_on_bat_ker_own", lay, &b0own, &groups);
        // Rank of relR1 (+ ia) on the read support, per reading.
        let rel_rank = |rd: usize| -> usize {
            let mut e = Ech::new(bw);
            for (n, fs) in groups.iter() {
                if n.starts_with("line[") && *n != format!("line[{}]", READINGS[rd]) {
                    continue;
                }
                for f in fs {
                    e.insert(f.clone());
                }
            }
            e.rank
        };
        let ranks: Vec<usize> = (0..3).map(rel_rank).collect();
        // V_G.
        let mut vg = Ech::new(bw);
        lane_elim(
            ln.count(10),
            |i| {
                let (o, b, rd) = ln.bal(10, i);
                let mut vv = o;
                vv.extend(flatten(&rd));
                (vv, wflat(&b))
            },
            |c| {
                vg.insert(c);
            },
        );
        let mut join = copied_ech(&vg);
        for r in ech_rows(&b0own) {
            join.insert(r);
        }
        // BCondG_R1 on the read support: B0R1 ∩ {ia = 0} <= V_G with the reading that holds.
        let holds_reading: Vec<usize> = (0..3).filter(|&rd| groups.iter().find(|(n, _)| *n == format!("line[{}]", READINGS[rd])).map(|(_, fs)| fs.iter().all(|f| ech_rows(&b0own).iter().all(|r| dotm(f, r) == M31::ZERO))).unwrap()).collect();
        let b0r1_dim: Vec<usize> = ranks.iter().map(|r| bw - r).collect();
        let vg_in_b0own = join.rank == b0own.rank;
        let b0own_le_vg = join.rank == vg.rank;
        let bcondg: Vec<bool> = (0..3).map(|rd| holds_reading.contains(&rd) && vg.rank == b0r1_dim[rd]).collect();
        println!(
            "Z9B_BCOND {glabel} bat_ker_own_rank={} ia_pivots={ia_piv} V_G_rank={} V_G_inside_bat_ker_own={vg_in_b0own} B0own_le_V_G={b0own_le_vg} relR1_plus_ia_rank_per_reading={ranks:?} dim_B0R1_on_read_support_per_reading={b0r1_dim:?} readings_annihilating={:?} BCondG_R1_per_reading={bcondg:?} unexplained_annihilator={un} unopened_folded_cells_in_ker_relR1={}",
            b0own.rank, vg.rank, holds_reading.iter().map(|&r| READINGS[r]).collect::<Vec<_>>(), 262144 - lay.nf
        );
        println!("Z9B_GAMMA_DONE {glabel} seconds={:.3}", start.elapsed().as_secs_f64());
    }
    println!("Z9B_DONE {label} wall_seconds={:.3}", start.elapsed().as_secs_f64());
}

// ---------------------------------------------------------------- R1-P prototype
/// The P_R1 honest-prover check (DESIGN-R1-P §1), timed per conjunct, on one
/// challenge (structure, vector, query set, gamma limb set). Public inputs only.
pub(crate) fn main_r1p() {
    let args: Vec<_> = std::env::args().collect();
    let get = |k: &str| args.windows(2).find(|x| x[0] == k).map(|x| x[1].clone());
    let s = get("--structure").unwrap_or("A".into());
    let v: usize = get("--vector").unwrap_or("0".into()).parse().unwrap();
    let qspec = get("--qset").unwrap_or("actual".into());
    let gi: usize = get("--gamma").unwrap_or("0".into()).parse().unwrap();
    let t0 = Instant::now();
    let lap = |t: &mut Instant| -> f64 { let e = t.elapsed().as_secs_f64(); *t = Instant::now(); e };
    let mut tt = Instant::now();
    let pi = d18_transport();
    z5::set_transport(pi);
    let t = trial(v);
    let a = alpha_for(&s, v, &t.a);
    let qs = query_set(&qspec, &t.qs);
    let op = opening_challenges(v, gi);
    let label = format!("structure={s} vector={v} qset={qspec} gamma={gi}");
    // §1.2 field and sampler conjuncts.
    let half_ok = a[9] != QM31::from_m31(M31(2).inv());
    let sem_k4 = true; // QM31 by construction (qm31_sample); the probe carries QM31 values.
    let mut dq = qs.clone();
    dq.dedup();
    let query_card = qs.len() == 22 && dq.len() == 22;
    let t_field = lap(&mut tt);
    // §1.1 shared precomputation.
    let lay = Lay::new(&qs);
    let bw = lay.bw;
    let (br, gr) = raw_c(&a, &t.z, &qs);
    let zk = [[t.z[0].x, t.z[0].y], [t.z[1].x, t.z[1].y]];
    let wts = r1::Weights::new(&a, &zk);
    let w = wts.materialize(op.kappa, inactive_fn);
    let geo = Geo::new();
    let phi = unit_functionals(&geo, &w, &op, &lay);
    let beta: Vec<Vec<W>> = (0..N).map(|r| phi[usize::from(pi[r])].clone()).collect();
    let gpow = (0..29).map(|l| op.gamma.pow(l as u64)).collect();
    let tail: Vec<_> = (0..N).map(|r| tail_row(&a, r)).collect();
    let cx = Ctx { a, br, gr, tail, beta, gpow, lay: Lay::new(&qs) };
    let ln = Lanes::new(&cx);
    let t_pre = lap(&mut tt);
    // §1.5 lifts.
    let obs_rank = |src: &[Vec<M31>], width: usize| rank_of(width, src.iter().cloned());
    let bal_f = |r: usize| -> Vec<M31> { if inactive(r) { sub_vec(&cx.br[r][1..], &cx.br[1023][1..], |x, y| x.sub(y)) } else { cx.br[r][1..].to_vec() } };
    let w_f = obs_rank(&(0..N).filter(|&r| r != 1023).map(|r| bal_f(r)).collect::<Vec<_>>(), 112);
    let c1: Vec<bool> = (0..16)
        .map(|c| obs_rank(&(0..N).filter(|&r| r != 1023 && eligible(c, r)).map(|r| bal_f(r)).collect::<Vec<_>>(), 112) == w_f)
        .collect();
    let bal_k = |r: usize, k: usize| -> Vec<M31> {
        if inactive(r) { flatten(&scale(&sub_vec(&cx.gr[r][1..], &cx.gr[0][1..], |p, q| p.sub(q)), tower(k))) } else { flatten(&scale(&cx.gr[r][1..], tower(k))) }
    };
    let w_k = obs_rank(&(1..N).flat_map(|r| (0..4).map(move |k| (r, k))).map(|(r, k)| bal_k(r, k)).collect::<Vec<_>>(), 376);
    let p_k = obs_rank(&(1..N).filter(|&r| inactive(r)).flat_map(|r| (0..4).map(move |k| (r, k))).map(|(r, k)| bal_k(r, k)).collect::<Vec<_>>(), 376);
    let h1 = p_k == w_k;
    let t_lifts = lap(&mut tt);
    // §1.4 BCondG_R1.
    let mut vg = Ech::new(bw);
    lane_elim(ln.count(10), |i| { let (o, b, rd) = ln.bal(10, i); let mut vv = o; vv.extend(flatten(&rd)); (vv, wflat(&b)) }, |c| { vg.insert(c); });
    let wd = weights_design(&a, &t.z, op.kappa);
    let dr = design_relations(&wd, &op, &qs, &cx.lay);
    let mut relset = Ech::new(bw);
    let mut rels: Vec<&Rel> = vec![&dr.s2a, &dr.s2b, &dr.s1];
    rels.extend(dr.circ.iter());
    rels.extend(dr.line[1].iter());
    for r in &rels {
        for f in r.limb_functionals(bw) {
            relset.insert(f);
        }
    }
    // read support excludes the inactive-sum cell (8 limbs, identically 0 on V_G).
    let dim_b0 = (bw - 8) - relset.rank;
    let vg_rows = ech_rows(&vg);
    let vg_in_b0 = rels.iter().all(|r| vg_rows.iter().all(|y| r.eval(&wvals(y)) == W::ZERO));
    let bcondg = vg.rank == dim_b0 && vg_in_b0;
    let t_bcond = lap(&mut tt);
    // §1.3 QPrime_R1.
    let mut rimg = Ech::new(RW);
    for li in 0..LANES {
        lane_elim(ln.count(li), |i| { let (o, _, r) = ln.bal(li, i); (o, flatten(&r)) }, |c| { rimg.insert(c); });
    }
    let chain: Vec<Vec<M31>> = (0..RW)
        .map(|i| {
            let mut u = vec![M31::ZERO; RW];
            u[i] = M31::ONE;
            let q = unflat(&u);
            let ph = final_value(&q, &a);
            flatten(&normalize_d(&q, ph, &a).expect("alpha9 = 1/2 is excluded by HalfOK"))
        })
        .collect();
    let qprime = chain.iter().all(|c| rimg.residual(c.clone()).iter().all(|x| *x == M31::ZERO));
    let t_qprime = lap(&mut tt);
    let p = half_ok && sem_k4 && query_card && qprime && bcondg && c1.iter().all(|x| *x) && h1;
    println!(
        "R1P_RESULT {label} P_R1={p} HalfOK={half_ok} SemK4={sem_k4} QueryCard={query_card} QPrime_R1={qprime} rank_R_ker_own={} BCondG_R1={bcondg} dim_V_G={} dim_B0R1p={dim_b0} V_G_in_B0R1p={vg_in_b0} C1Lift={c1:?} rank_obs_Wsem={w_f} H1Lift={h1} rank_obs_Ph1={p_k} rank_obs_Wh1={w_k} distinct_parents={}",
        rimg.rank, vg.rank, lay.nf / 4
    );
    println!(
        "R1P_TIME {label} field={t_field:.3} precompute={t_pre:.3} lifts={t_lifts:.3} bcondg={t_bcond:.3} qprime={t_qprime:.3} total={:.3}",
        t0.elapsed().as_secs_f64()
    );
}

// ---------------------------------------------------------------- D38.5 certificates
#[path = "z9c.rs"]
pub(crate) mod z9c;
