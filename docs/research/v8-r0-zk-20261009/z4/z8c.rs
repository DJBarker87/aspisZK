//! Z8c (T2b-2b design §3.3, LOG "Lead acceptance of the T2b-2b design as a
//! proposal (2026-10-15)"): the silent-rank gate on the BALANCED Lean mask
//! space, with Z8's WideExact batching and real linearPayload silence
//! coordinates. Exact M31/QM31/WideExact arithmetic. Not a Lean proof.
//!
//! Balancing (R0Z/MaskLayout.lean `balance 0`, `maskOnlyColumns`, `dWord`,
//! and lane 27 in `applyAff`): row 0 of every mask lane (mask-only 16..25,
//! G = 27, D = 28; each limb of G and D) is minus the sum of the other
//! copy-inactive rows. The balanced word space of a lane is therefore spanned
//! by e_r for active r and e_r - e_0 for inactive r != 0 (one source per raw
//! tape coordinate r != 0; the raw row-0 coordinate is overwritten and has no
//! effect). No batched-.inactiveSum proxy: on these sources .inactiveSum is
//! identically 0 and is checked to be so.
//!
//! Everything between this header and `// ---- Z8b helpers ----` is copied
//! verbatim from z8.rs (print tags renamed Z8_ -> Z8C_, as z8b.rs did; STRUCTURES
//! and alpha_for extended by K, L, M, appended so that A, B, I, J keep their
//! seeds). `lane_kernel`, `slice_from`, `rank_of`, `d_own` are copied verbatim
//! from z8b.rs. Rank routines: probe.rs's Ech, initial_zero, copied_ech,
//! summarize, pass_count (unchanged). New code follows `// ---- Z8c ----`.
use super::*;
use aspis_core::field::WideExact as W;
use aspis_core::r0::{
    basis::{BasisSize, NaturalBasis},
    chord::{self, FunctionalWeights, Secant},
    encoder, fold, opening, prover,
    transport::ROW_TO_COEFFICIENT,
};

const MASTER: u64 = 0x5348f0b9a87835d0;
const STRUCT_SEED: u64 = 0x5a38_d20b_2026_1013;
const OPEN_SEED: u64 = 0x5a38_0be0_2026_1013;
const STRUCTURES: [&str; 7] = ["A", "B", "I", "J", "K", "L", "M"];
const NB: usize = 264; // inactiveSum + 7 openingCoeff + 256 finalCoeff
const BW: usize = NB * 8; // batched M31 coordinates
const RW: usize = 1084; // round coordinates (Z4c layout)
const TW: usize = BW + RW;
const THREADS: usize = 4;

struct Trial {
    a: [QM31; 10],
    z: [Point<QM31>; 2],
    qs: Vec<usize>,
    ch: Challenges,
    tapes: Vec<Trace>,
}
/// Exact replay of z4c_main's RNG consumption (copied from z7.rs `trial`).
fn trial(trial: usize) -> Trial {
    let trial_seed = MASTER.wrapping_add((trial as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15));
    let mut rng = Rng(trial_seed);
    let a = std::array::from_fn(|_| rng.q());
    let z = [circle(rng.q()), circle(rng.q())];
    let sets = query_sets(&mut rng);
    let ch = Challenges {
        lambda: rng.q(),
        chi: rng.q(),
        theta: rng.q(),
        zc: std::array::from_fn(|_| rng.q()),
        mu: rng.q(),
        eta: rng.q(),
    };
    println!("TRIAL_SEED trial={trial} seed={trial_seed:#x}");
    println!("CHALLENGE trial={trial} alpha={a:?} semantic={ch:?} circle={z:?} queries={:?}", sets[0].1);
    let tapes = (0..5)
        .map(|_| {
            (0..17)
                .map(|c| {
                    (0..N)
                        .map(|r| {
                            if c < 16 && eligible(c, r) {
                                QM31::from_m31(rng.m())
                            } else if c == 16 && inactive(r) {
                                rng.q()
                            } else {
                                QM31::ZERO
                            }
                        })
                        .collect()
                })
                .collect()
        })
        .collect();
    Trial { a, z, qs: sets[0].1.clone(), ch, tapes }
}

fn l4(x: QM31) -> [u32; 4] {
    limbs(x).map(|v| v.0)
}
fn unflat(v: &[M31]) -> Vec<QM31> {
    v.chunks(4)
        .map(|c| QM31 { c0: CM31::new(c[0], c[1]), c1: CM31::new(c[2], c[3]) })
        .collect()
}
fn half() -> QM31 {
    QM31::from_m31(M31(2).inv())
}
fn admissible(a: &[QM31; 10]) -> bool {
    a.iter().all(|x| *x != QM31::ZERO && *x != QM31::ONE) && a[9] != half()
}
fn f_nontrivial(rng: &mut Rng, last: bool) -> QM31 {
    loop {
        let x = QM31::from_m31(rng.m());
        if x != QM31::ZERO && x != QM31::ONE && !(last && x == half()) {
            return x;
        }
    }
}
fn k2_nontrivial(rng: &mut Rng, last: bool) -> QM31 {
    loop {
        let x = QM31 { c0: CM31::new(rng.m(), rng.m()), c1: CM31::new(M31::ZERO, M31::ZERO) };
        if x != QM31::ZERO && x != QM31::ONE && !(last && x == half()) {
            return x;
        }
    }
}
/// A: Z4c alpha. B: all alpha_i in F\{0,1}. I: all alpha_i in K2 = F(i)\{0,1}.
/// J: alpha_0 Z4c (uniform in QM31), alpha_1..6 in F\{0,1}, alpha_7..9 Z4c.
/// Z8c additions (seeds of A, B, I, J unchanged: new structures are appended):
/// K: alpha_2, alpha_3 in F\{0,1}, others Z4c.  L: alpha_0..5 in F\{0,1},
/// alpha_6..9 Z4c (alpha_6 checked outside K2).  M: alpha_3..6 in F\{0,1}, others Z4c.
fn alpha_for(s: &str, v: usize, base: &[QM31; 10]) -> [QM31; 10] {
    let si = STRUCTURES.iter().position(|x| *x == s).unwrap() as u64;
    let mut rng = Rng(STRUCT_SEED.wrapping_add((si * 64 + v as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15)));
    let mut a = *base;
    match s {
        "A" => {}
        "B" => (0..10).for_each(|i| a[i] = f_nontrivial(&mut rng, i == 9)),
        "I" => (0..10).for_each(|i| a[i] = k2_nontrivial(&mut rng, i == 9)),
        "J" => (1..7).for_each(|i| a[i] = f_nontrivial(&mut rng, false)),
        "K" => (2..4).for_each(|i| a[i] = f_nontrivial(&mut rng, false)),
        "L" => {
            (0..6).for_each(|i| a[i] = f_nontrivial(&mut rng, false));
            assert!(!in_k2(a[6]), "structure L needs alpha_6 outside K2");
        }
        "M" => (3..7).for_each(|i| a[i] = f_nontrivial(&mut rng, false)),
        _ => panic!("unknown structure {s}"),
    }
    assert!(admissible(&a), "alpha admissibility");
    a
}
fn lambda_dims(a: &[QM31; 10]) -> Vec<usize> {
    (0..10)
        .map(|j| {
            let mut e = Ech::new(4);
            for l in 0..1usize << j {
                let x = (0..j).fold(QM31::ONE, |v, i| {
                    v.mul(if l >> i & 1 == 1 { a[i] } else { QM31::ONE.sub(a[i]) })
                });
                e.insert(limbs(x).to_vec());
            }
            e.rank
        })
        .collect()
}

/// `last_coeff`'s chain reconstruction, returning all ten polys (copied from z7.rs).
fn round_polys(v: &[QM31], a: &[QM31; 10]) -> Vec<[QM31; 28]> {
    let mut prev = v[0];
    let mut out = vec![];
    for j in 0..10 {
        let mut co = [QM31::ZERO; 28];
        co[0] = v[1 + 27 * j];
        co[2..].copy_from_slice(&v[2 + 27 * j..28 + 27 * j]);
        co[1] = prev
            .sub(co[0].add(co[0]))
            .sub(co[2..].iter().fold(QM31::ZERO, |v, x| v.add(*x)));
        prev = co.iter().rev().fold(QM31::ZERO, |v, x| v.mul(a[j]).add(*x));
        out.push(co);
    }
    out
}
/// Per-round projection ranks (copied from z7.rs).
struct Proj {
    full: Vec<Ech<M31>>,
    limb: Vec<Vec<Ech<M31>>>,
}
impl Proj {
    fn of(e: &Ech<M31>, a: &[QM31; 10]) -> Self {
        let mut p = Proj {
            full: (0..10).map(|_| Ech::new(112)).collect(),
            limb: (0..10).map(|_| (0..4).map(|_| Ech::new(28)).collect()).collect(),
        };
        for b in e.p.iter().flatten() {
            for (j, co) in round_polys(&unflat(b), a).iter().enumerate() {
                p.full[j].insert(flatten(co));
                for k in 0..4 {
                    p.limb[j][k].insert(co.iter().map(|x| limbs(*x)[k]).collect());
                }
            }
        }
        p
    }
    fn full_ranks(&self) -> Vec<usize> {
        self.full.iter().map(|e| e.rank).collect()
    }
    fn limb_ranks(&self) -> Vec<[usize; 4]> {
        self.limb.iter().map(|l| std::array::from_fn(|k| l[k].rank)).collect()
    }
}

fn wq(x: QM31) -> W {
    W::from_qm31(x)
}
fn wlimbs(x: W) -> [M31; 8] {
    x.to_limbs().map(M31)
}
fn wpt(p: Point<QM31>) -> Point<W> {
    Point { x: wq(p.x), y: wq(p.y) }
}
fn w_uniform(rng: &mut Rng) -> W {
    W::new(rng.q(), rng.q())
}
struct Opening {
    gamma: W,
    kappa: W,
    tau: W,
    fold: W,
}
/// ch.opening 0..3, uniform in WideExact; one stream per vector (shared by
/// all structures of that vector); gamma resampled at zero as the sampler does.
fn opening_challenges(v: usize) -> Opening {
    let mut rng = Rng(OPEN_SEED.wrapping_add((v as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15)));
    let gamma = loop {
        let g = w_uniform(&mut rng);
        if g != W::ZERO {
            break g;
        }
    };
    Opening { gamma, kappa: w_uniform(&mut rng), tau: w_uniform(&mut rng), fold: w_uniform(&mut rng) }
}

/// Lean `totalWeights` with Lean `weights` (Rust OpeningData::weights + kappa^4 libraWeight).
fn total_weights(basis: &NaturalBasis, a: &[QM31; 10], z: [Point<W>; 2], op: &Opening) -> [W; 1024] {
    let aw = a.map(wq);
    let pts = opening::points_from_alphas(&aw);
    // Orientation check: Rust row_eq_weight(points_from_alphas) == Z4c eq(points).
    let zp = points(a);
    for j in 0..3 {
        let rw = opening::row_eq_weight(&pts[j]);
        for r in 0..N {
            assert_eq!(rw[r], wq(eq(&zp[j], r)), "eq orientation j={j} r={r}");
        }
    }
    let eqs = pts.map(|p| opening::eq_weight(&p));
    let ind = opening::indicator();
    let k = opening::powers::<5>(op.kappa);
    let w: [W; 1024] = std::array::from_fn(|j| {
        ind[j]
            .add(k[1].mul(eqs[0][j]))
            .add(k[2].mul(eqs[1][j]))
            .add(k[3].mul(eqs[2][j]))
            .add(k[4].mul(wq(h_weight(a, j))))
    });
    let line = Secant::from_points(z[0], z[1]);
    let qw = chord::quotient_weights(basis, line, &w).expect("quotient_weights");
    let e1 = FunctionalWeights::e1::<W>(basis).expect("e1");
    let e2 = FunctionalWeights::e2(basis, line.b, line.c).expect("e2");
    std::array::from_fn(|j| qw[j].add(op.tau.mul(e1[j])).add(op.tau.mul(op.tau).mul(e2[j])))
}
fn ood_pair(m: &[W; 1024], z: [Point<W>; 2]) -> [W; 2] {
    [encoder::eval_message(m, z[0]), encoder::eval_message(m, z[1])]
}
/// phi[k] = (round_polynomial(Q e_k, total) [7], fold_message(op.fold, Q e_k) [256])
/// for every natural coefficient unit e_k (Q = prover::quotient, column-wise).
fn unit_functionals(basis: &NaturalBasis, z: [Point<W>; 2], total: &[W; 1024], op: &Opening) -> Vec<[W; NB - 1]> {
    let ks: Vec<usize> = (0..1024).collect();
    let chunk = ks.len().div_ceil(THREADS);
    std::thread::scope(|s| {
        let hs: Vec<_> = ks
            .chunks(chunk)
            .map(|part| {
                s.spawn(move || {
                    part.iter()
                        .map(|&k| {
                            let mut e = [W::ZERO; 1024];
                            e[k] = W::ONE;
                            let q = prover::quotient(basis, z, &e, ood_pair(&e, z))
                                .unwrap_or_else(|err| panic!("STOP quotient unit k={k} error={err:?}"));
                            let rp = prover::round_polynomial(&q, total);
                            let f = fold::fold_message(op.fold, &q);
                            let mut out = [W::ZERO; NB - 1];
                            out[..7].copy_from_slice(&rp);
                            out[7..].copy_from_slice(&f);
                            out
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        hs.into_iter().flat_map(|h| h.join().unwrap()).collect()
    })
}

struct Ctx {
    a: [QM31; 10],
    br: Vec<Vec<M31>>,
    gr: Vec<Vec<QM31>>,
    tail: Vec<Vec<QM31>>,
    beta: Vec<[W; NB]>, // row-indexed
    gpow: Vec<W>,       // gamma^lane, lane 0..28
}
impl Ctx {
    /// Batched payload of x at row r of physical lane `lane`.
    fn batched(&self, lane: usize, x: W, r: usize) -> Vec<W> {
        let g = self.gpow[lane].mul(x);
        self.beta[r].iter().map(|b| g.mul(*b)).collect()
    }
}
fn wflat(v: &[W]) -> Vec<M31> {
    v.iter().flat_map(|x| wlimbs(*x)).collect()
}
fn sub_vec<T: Copy>(a: &[T], b: &[T], f: impl Fn(T, T) -> T) -> Vec<T> {
    a.iter().zip(b).map(|(x, y)| f(*x, *y)).collect()
}

/// One lane's sources, eliminated on its own per-lane coordinates (as Z4c's
/// lane_eliminate does), carrying [batched (2112) | round (1084)] in M31.
/// Kernel carries are inserted into `global`; returns the carried particular
/// solution for each per-lane target (which must lie in the lane's coordinate span).
fn lane_stage(
    count: usize,
    mut source: impl FnMut(usize) -> (Vec<M31>, Vec<M31>),
    targets: &[Vec<M31>],
    global: &mut Ech<M31>,
) -> Vec<Vec<M31>> {
    let mut piv: Vec<Option<(Vec<M31>, Vec<M31>)>> = vec![];
    for i in 0..count {
        let (mut v, mut c) = source(i);
        if piv.is_empty() {
            piv = vec![None; v.len()];
        }
        let mut pivot = None;
        for i in 0..v.len() {
            if v[i] == M31::ZERO {
                continue;
            }
            if let Some((b, bc)) = &piv[i] {
                let s = v[i];
                for j in i..v.len() {
                    v[j] = v[j].sub(s.mul(b[j]));
                }
                for j in 0..TW {
                    c[j] = c[j].sub(s.mul(bc[j]));
                }
            } else {
                let inv = v[i].inv();
                for x in &mut v[i..] {
                    *x = x.mul(inv);
                }
                for x in &mut c {
                    *x = x.mul(inv);
                }
                pivot = Some(i);
                break;
            }
        }
        match pivot {
            Some(i) => piv[i] = Some((v, c)),
            None => {
                global.insert(c);
            }
        }
    }
    targets
        .iter()
        .map(|t| {
            let mut v = t.clone();
            let mut out = vec![M31::ZERO; TW];
            for i in 0..v.len() {
                if v[i] == M31::ZERO {
                    continue;
                }
                let (b, bc) = piv[i].as_ref().expect("per-lane target outside lane coordinate span");
                let s = v[i];
                for j in i..v.len() {
                    v[j] = v[j].sub(s.mul(b[j]));
                }
                for j in 0..TW {
                    out[j] = out[j].add(s.mul(bc[j]));
                }
            }
            out
        })
        .collect()
}
fn carry(batched: Vec<W>, round: &[QM31]) -> Vec<M31> {
    let mut c = wflat(&batched);
    c.extend(flatten(round));
    debug_assert_eq!(c.len(), TW);
    c
}
fn scale(v: &[QM31], x: QM31) -> Vec<QM31> {
    v.iter().map(|y| y.mul(x)).collect()
}
/// Mask-only lanes (F, all rows), G (K4, all rows) and D (K4, all rows).
fn pure_sources(cx: &Ctx, global: &mut Ech<M31>) {
    let a = &cx.a;
    for c in 0..10 {
        let lane = 16 + c;
        lane_stage(N, |r| (cx.br[r][1..].to_vec(), carry(cx.batched(lane, W::ONE, r), &round_row(a, r, c))), &[], global);
    }
    for (lane, g) in [(27usize, true), (28, false)] {
        lane_stage(
            4 * N,
            |i| {
                let (r, k) = (i / 4, i % 4);
                let x = tower(k);
                let rr = if g { round_row(a, r, 10) } else { cx.tail[r].clone() };
                (flatten(&scale(&cx.gr[r][1..], x)), carry(cx.batched(lane, wq(x), r), &scale(&rr, x)))
            },
            &[],
            global,
        );
    }
}
/// Semantic eligible sources (balanced vs row 1023) and H1 padding (inactive
/// rows, balanced vs row 0), with the per-pair witness-difference targets.
fn conditioned_sources(cx: &Ctx, traces: &[Trace], pairs: usize, global: &mut Ech<M31>) -> Vec<Vec<M31>> {
    let a = &cx.a;
    let mut sol = vec![vec![M31::ZERO; TW]; pairs];
    for c in 0..16 {
        let rows: Vec<usize> = (0..N).filter(|&r| r != 1023 && eligible(c, r)).collect();
        let tg: Vec<Vec<M31>> = (0..pairs)
            .map(|p| {
                let d: Vec<M31> = (0..N).map(|r| traces[2 * p][c][r].c0.a.sub(traces[2 * p + 1][c][r].c0.a)).collect();
                (1..113).map(|i| (0..N).fold(M31::ZERO, |s, r| s.add(d[r].mul(cx.br[r][i])))).collect()
            })
            .collect();
        let rd = round_row(a, 1023, 38 + c);
        let bd = cx.batched(c, W::ONE, 1023);
        let s = lane_stage(
            rows.len(),
            |i| {
                let r = rows[i];
                let rr = round_row(a, r, 38 + c);
                let bb = cx.batched(c, W::ONE, r);
                if inactive(r) {
                    (
                        sub_vec(&cx.br[r][1..], &cx.br[1023][1..], |x, y| x.sub(y)),
                        carry(sub_vec(&bb, &bd, |x, y| x.sub(y)), &sub_vec(&rr, &rd, |x, y| x.sub(y))),
                    )
                } else {
                    (cx.br[r][1..].to_vec(), carry(bb, &rr))
                }
            },
            &tg,
            global,
        );
        for p in 0..pairs {
            for j in 0..TW {
                sol[p][j] = sol[p][j].add(s[p][j]);
            }
        }
    }
    let rows: Vec<usize> = (1..N).filter(|&r| inactive(r)).collect();
    let tg: Vec<Vec<M31>> = (0..pairs)
        .map(|p| {
            let d: Vec<QM31> = (0..N).map(|r| traces[2 * p][16][r].sub(traces[2 * p + 1][16][r])).collect();
            flatten(&(1..95).map(|i| (0..N).fold(QM31::ZERO, |s, r| s.add(d[r].mul(cx.gr[r][i])))).collect::<Vec<_>>())
        })
        .collect();
    let zero = vec![QM31::ZERO; 271];
    let s = lane_stage(
        4 * rows.len(),
        |i| {
            let (r, k) = (rows[i / 4], i % 4);
            let x = tower(k);
            let b = sub_vec(&cx.batched(26, wq(x), r), &cx.batched(26, wq(x), 0), |p, q| p.sub(q));
            (flatten(&scale(&sub_vec(&cx.gr[r][1..], &cx.gr[0][1..], |p, q| p.sub(q)), x)), carry(b, &zero))
        },
        &tg,
        global,
    );
    for p in 0..pairs {
        for j in 0..TW {
            sol[p][j] = sol[p][j].add(s[p][j]);
        }
    }
    sol
}
/// Rows of `e` with pivot >= from, sliced to the round part [BW..].
fn slice_image(e: &Ech<M31>, from: usize) -> Ech<M31> {
    let mut out = Ech::new(RW);
    for (i, row) in e.p.iter().enumerate() {
        if let Some(v) = row {
            if i >= from {
                out.insert(v[BW..].to_vec());
            }
        }
    }
    out
}
/// Reduce by pivots < BW only (the batched coordinates).
fn batched_reduce(e: &Ech<M31>, mut v: Vec<M31>) -> Vec<M31> {
    for i in 0..BW {
        if v[i] == M31::ZERO {
            continue;
        }
        if let Some(b) = &e.p[i] {
            let s = v[i];
            for j in i..v.len() {
                v[j] = v[j].sub(s.mul(b[j]));
            }
        }
    }
    v
}
fn report(label: &str, kind: &str, total: usize, p: &Proj) {
    println!(
        "Z8C_RANKS {label} kind={kind} total={total} round_full={:?} round_limb={:?}",
        p.full_ranks(),
        p.limb_ranks()
    );
}

/// Direct check of the column-wise decomposition: for random words on lanes
/// 16 (F) and 27, 28 (K4), the Rust pipeline on whole columns (quotient per
/// lane, gamma-batched, round_polynomial with total weights, fold_message,
/// v_honest-style inactive sum) equals the sum of per-row batched vectors.
fn decomposition_check(cx: &Ctx, basis: &NaturalBasis, z: [Point<W>; 2], total: &[W; 1024], op: &Opening, seed: u64) {
    let mut rng = Rng(seed);
    let mut q = [W::ZERO; 1024];
    let mut inactive_sum = W::ZERO;
    let mut expected = vec![W::ZERO; NB];
    for lane in [16usize, 27, 28] {
        let rows: [W; 1024] = std::array::from_fn(|_| if lane == 16 { wq(QM31::from_m31(rng.m())) } else { wq(rng.q()) });
        let coeffs = aspis_core::r0::transport::to_coefficients(&rows);
        let ql = prover::quotient(basis, z, &coeffs, ood_pair(&coeffs, z)).expect("column quotient");
        for i in 0..1024 {
            q[i] = q[i].add(cx.gpow[lane].mul(ql[i]));
        }
        for r in 0..N {
            if inactive(r) {
                inactive_sum = inactive_sum.add(cx.gpow[lane].mul(rows[r]));
            }
            for (e, b) in expected.iter_mut().zip(cx.batched(lane, rows[r], r)) {
                *e = e.add(b);
            }
        }
    }
    let rp = prover::round_polynomial(&q, total);
    let f = fold::fold_message(op.fold, &q);
    let mut direct = vec![inactive_sum];
    direct.extend_from_slice(&rp);
    direct.extend_from_slice(&f);
    assert_eq!(direct, expected, "column-wise decomposition");
    println!("Z8C_CHECK decomposition lanes=[16,27,28] whole_column_pipeline_equals_rowwise_sum=true coordinates={NB}");
}


// ---- Z8b helpers ---- (copied verbatim from z8b.rs)
use aspis_core::r0::transport::COEFFICIENT_TO_ROW;

const DW: usize = 376; // D's own-silence functionals: 94 K4-valued = 376 M31 limbs
const SW: usize = BW + DW + RW; // [batched | D own | round]

/// [batched limbs | D-own limbs | round limbs].
fn gen3(batched: Vec<W>, down: Vec<M31>, round: &[QM31]) -> Vec<M31> {
    let mut v = wflat(&batched);
    v.extend(down);
    v.extend(flatten(round));
    assert_eq!(v.len(), SW);
    v
}
fn d_own(cx: &Ctx, r: usize, x: QM31) -> Vec<M31> {
    flatten(&scale(&cx.gr[r][1..], x))
}
/// z8.rs `lane_stage` with the carry width taken from the source and the
/// kernel carries handed to `sink` (no targets).
fn lane_kernel(count: usize, mut source: impl FnMut(usize) -> (Vec<M31>, Vec<M31>), mut sink: impl FnMut(Vec<M31>)) {
    let mut piv: Vec<Option<(Vec<M31>, Vec<M31>)>> = vec![];
    for i in 0..count {
        let (mut v, mut c) = source(i);
        if piv.is_empty() {
            piv = vec![None; v.len()];
        }
        let mut pivot = None;
        for i in 0..v.len() {
            if v[i] == M31::ZERO {
                continue;
            }
            if let Some((b, bc)) = &piv[i] {
                let s = v[i];
                for j in i..v.len() {
                    v[j] = v[j].sub(s.mul(b[j]));
                }
                for j in 0..c.len() {
                    c[j] = c[j].sub(s.mul(bc[j]));
                }
            } else {
                let inv = v[i].inv();
                for x in &mut v[i..] {
                    *x = x.mul(inv);
                }
                for x in &mut c {
                    *x = x.mul(inv);
                }
                pivot = Some(i);
                break;
            }
        }
        match pivot {
            Some(i) => piv[i] = Some((v, c)),
            None => sink(c),
        }
    }
}
fn slice_from(e: &Ech<M31>, from: usize, offset: usize, width: usize) -> Ech<M31> {
    let mut out = Ech::new(width);
    for (i, row) in e.p.iter().enumerate() {
        if let (Some(v), true) = (row, i >= from) {
            out.insert(v[offset..].to_vec());
        }
    }
    out
}
fn rank_of(width: usize, vs: impl Iterator<Item = Vec<M31>>) -> usize {
    let mut e = Ech::new(width);
    for v in vs {
        e.insert(v);
    }
    e.rank
}
fn g_lane_coords(cx: &Ctx, r: usize, x: QM31, with_inactive: bool) -> Vec<M31> {
    let mut v = d_own(cx, r, x);
    if with_inactive {
        v.extend(if inactive(r) { limbs(x) } else { [M31::ZERO; 4] });
    }
    v
}


// ---- Z8c ----


fn in_k2(x: QM31) -> bool {
    x.c1 == CM31::new(M31::ZERO, M31::ZERO)
}
/// Good3 (design §1.2): at least three of alpha_0..alpha_3 outside K2.
fn good3(a: &[QM31; 10]) -> bool {
    (0..4).filter(|&i| !in_k2(a[i])).count() >= 3
}
const LANES: usize = 12; // mask-only 0..9 (phys 16..25), G (27), D (28)
fn lane_name(li: usize) -> String {
    match li {
        0..=9 => format!("m{li}_e{}", EXP[li]),
        10 => "G".into(),
        _ => "D".into(),
    }
}
fn phys(li: usize) -> usize {
    match li {
        0..=9 => 16 + li,
        10 => 27,
        _ => 28,
    }
}
fn per_row(li: usize) -> usize {
    if li < 10 { 1 } else { 4 }
}
fn own_width(li: usize) -> usize {
    if li < 10 { 112 } else { DW }
}
/// Own-functional blocks in limbs (same boundaries for F and K4 lanes):
/// claim0, claim1, claim2, extra, ood(2), opened(88).
fn own_blocks(li: usize) -> [(&'static str, usize, usize); 6] {
    [("claim0", 0, 4), ("claim1", 4, 8), ("claim2", 8, 12), ("extra", 12, 16), ("ood", 16, 24), ("opened", 24, own_width(li))]
}
type Src = (Vec<M31>, Vec<W>, Vec<QM31>); // (own limbs, batched NB values, round 271)
struct Lanes<'a> {
    cx: &'a Ctx,
    rr: Vec<Vec<Vec<QM31>>>, // [lane][row] unscaled round vector (round_row / tail_row)
    zero: Vec<Vec<Src>>,     // raw source at row 0, per lane and limb
}
impl<'a> Lanes<'a> {
    fn new(cx: &'a Ctx) -> Self {
        let a = cx.a;
        let rr: Vec<Vec<Vec<QM31>>> = std::thread::scope(|s| {
            let hs: Vec<_> = (0..LANES)
                .map(|li| {
                    s.spawn(move || {
                        (0..N)
                            .map(|r| if li == 11 { tail_row(&a, r) } else { round_row(&a, r, li) })
                            .collect::<Vec<_>>()
                    })
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let mut l = Lanes { cx, rr, zero: vec![] };
        l.zero = (0..LANES).map(|li| (0..per_row(li)).map(|k| l.raw(li, 0, k)).collect()).collect();
        l
    }
    /// Unbalanced unit source: value x (1 for F lanes, tower(k) for K4 lanes) at row r.
    fn raw(&self, li: usize, r: usize, k: usize) -> Src {
        let cx = self.cx;
        if li < 10 {
            (cx.br[r][1..].to_vec(), cx.batched(phys(li), W::ONE, r), self.rr[li][r].clone())
        } else {
            let x = tower(k);
            (d_own(cx, r, x), cx.batched(phys(li), wq(x), r), scale(&self.rr[li][r], x))
        }
    }
    fn count(&self, li: usize) -> usize {
        (N - 1) * per_row(li)
    }
    /// Balanced source i: row r = i / per_row + 1, limb i % per_row;
    /// e_r for active r, e_r - e_0 for inactive r (Lean `balance 0`).
    fn row_of(&self, li: usize, i: usize) -> (usize, usize) {
        (i / per_row(li) + 1, i % per_row(li))
    }
    fn bal(&self, li: usize, i: usize) -> Src {
        let (r, k) = self.row_of(li, i);
        let s = self.raw(li, r, k);
        if !inactive(r) {
            return s;
        }
        let z = &self.zero[li][k];
        (
            sub_vec(&s.0, &z.0, |x, y| x.sub(y)),
            sub_vec(&s.1, &z.1, |x, y| x.sub(y)),
            sub_vec(&s.2, &z.2, |x, y| x.sub(y)),
        )
    }
}

/// z8b `lane_kernel`, additionally returning the pivot rows (an echelon basis
/// of the image of the eliminated coordinates v).
fn lane_elim(count: usize, mut source: impl FnMut(usize) -> (Vec<M31>, Vec<M31>), mut sink: impl FnMut(Vec<M31>)) -> Vec<Vec<M31>> {
    let mut piv: Vec<Option<(Vec<M31>, Vec<M31>)>> = vec![];
    for i in 0..count {
        let (mut v, mut c) = source(i);
        if piv.is_empty() {
            piv = vec![None; v.len()];
        }
        let mut pivot = None;
        for i in 0..v.len() {
            if v[i] == M31::ZERO {
                continue;
            }
            if let Some((b, bc)) = &piv[i] {
                let s = v[i];
                for j in i..v.len() {
                    v[j] = v[j].sub(s.mul(b[j]));
                }
                for j in 0..c.len() {
                    c[j] = c[j].sub(s.mul(bc[j]));
                }
            } else {
                let inv = v[i].inv();
                for x in &mut v[i..] {
                    *x = x.mul(inv);
                }
                for x in &mut c {
                    *x = x.mul(inv);
                }
                pivot = Some(i);
                break;
            }
        }
        match pivot {
            Some(i) => piv[i] = Some((v, c)),
            None => sink(c),
        }
    }
    piv.into_iter().flatten().map(|(v, _)| v).collect()
}
fn ech_rows(e: &Ech<M31>) -> Vec<Vec<M31>> {
    e.p.iter().flatten().cloned().collect()
}
fn block_ranks(li: usize, carries: &[Vec<M31>]) -> Vec<(String, usize)> {
    let mut out = vec![("all".to_string(), rank_of(own_width(li), carries.iter().cloned()))];
    for (n, s, e) in own_blocks(li) {
        out.push((n.to_string(), rank_of(e - s, carries.iter().map(|c| c[s..e].to_vec()))));
    }
    out
}
fn fmt_ranks(v: &[(String, usize)]) -> String {
    v.iter().map(|(n, r)| format!("{n}:{r}")).collect::<Vec<_>>().join(",")
}

// Batched coordinate index: 0 = .inactiveSum, 1..=7 = .openingCoeff 0..6, 8.. = .finalCoeff 0..255.
fn bat_label(i: usize) -> String {
    match i {
        0 => "ia".into(),
        1..=7 => format!("h{}", i - 1),
        _ => format!("f{}", i - 8),
    }
}
fn wunit(m: usize) -> W {
    let mut l = [0u32; 8];
    l[m] = 1;
    W::from_limbs(l).unwrap()
}
fn wvals(limbs: &[M31]) -> Vec<W> {
    limbs.chunks(8).map(|c| W::from_limbs(std::array::from_fn(|i| c[i].0)).unwrap()).collect()
}
/// A K-linear relation on the batched coordinates: sum_i c_i * y_i.
struct Rel {
    name: String,
    c: Vec<(usize, W)>,
}
impl Rel {
    fn eval(&self, y: &[W]) -> W {
        self.c.iter().fold(W::ZERO, |s, (i, c)| s.add(c.mul(y[*i])))
    }
    /// The 8 F-functionals limb_k(sum c_i y_i) on the BW limb coordinates.
    fn limb_functionals(&self) -> Vec<Vec<M31>> {
        (0..8)
            .map(|k| {
                let mut v = vec![M31::ZERO; BW];
                for (i, c) in &self.c {
                    for m in 0..8 {
                        v[8 * i + m] = v[8 * i + m].add(M31(c.mul(wunit(m)).to_limbs()[k]));
                    }
                }
                v
            })
            .collect()
    }
}
/// (S1) check_v2 / round_eval, (S2) round_boundary (balanced form h0 + h4),
/// (S2u) unbalanced form h0 + h4 - quarter*ia, (S3_u) check_v1 / fold_encoded
/// at each queried fibre on own-silent tapes, the 14 low fold coordinates, and ia.
struct Relations {
    ia: Rel,
    s1: Rel,
    s2: Rel,
    s2u: Rel,
    s3: Vec<Rel>,
    low: Vec<Rel>,
}
fn relations(total: &[W; 1024], op: &Opening, qs: &[usize]) -> Relations {
    let quarter = fold::quarter::<W>();
    let df = fold::dual_fold(op.fold, total);
    let mut s1 = vec![];
    let mut p = W::ONE;
    for i in 0..7 {
        s1.push((1 + i, p));
        p = p.mul(op.fold);
    }
    for d in 0..256 {
        s1.push((8 + d, W::ZERO.sub(quarter.mul(df[d]))));
    }
    let s3 = qs
        .iter()
        .map(|&u| {
            let fib = FibreIndex::new(u).unwrap();
            let c = (0..256)
                .map(|d| {
                    let mut e = [W::ZERO; 256];
                    e[d] = W::ONE;
                    (8 + d, encoder::exact_final_encoder(&e, fib))
                })
                .collect();
            Rel { name: format!("S3_u{u}"), c }
        })
        .collect();
    Relations {
        ia: Rel { name: "ia".into(), c: vec![(0, W::ONE)] },
        s1: Rel { name: "S1".into(), c: s1 },
        s2: Rel { name: "S2".into(), c: vec![(1, W::ONE), (5, W::ONE)] },
        s2u: Rel { name: "S2u".into(), c: vec![(1, W::ONE), (5, W::ONE), (0, W::ZERO.sub(quarter))] },
        s3,
        low: (0..14).map(|d| Rel { name: format!("f{d}"), c: vec![(8 + d, W::ONE)] }).collect(),
    }
}
/// Null space of the row space of `img` (width BW) via back-substitution.
fn null_space(img: &Ech<M31>) -> Vec<Vec<M31>> {
    let n = img.p.len();
    let mut rows: Vec<Option<Vec<M31>>> = img.p.clone();
    let pivots: Vec<usize> = (0..n).filter(|&i| rows[i].is_some()).collect();
    for (pi, &i) in pivots.iter().enumerate().rev() {
        let ri = rows[i].clone().unwrap();
        for &j in &pivots[..pi] {
            let rj = rows[j].as_mut().unwrap();
            let s = rj[i];
            if s != M31::ZERO {
                for t in i..n {
                    rj[t] = rj[t].sub(s.mul(ri[t]));
                }
            }
        }
    }
    (0..n)
        .filter(|&f| rows[f].is_none())
        .map(|f| {
            let mut v = vec![M31::ZERO; n];
            v[f] = M31::ONE;
            for &p in &pivots {
                v[p] = M31::ZERO.sub(rows[p].as_ref().unwrap()[f]);
            }
            v
        })
        .collect()
}
fn support_labels(v: &[M31]) -> Vec<String> {
    let mut out = vec![];
    for i in 0..NB {
        let ls: Vec<usize> = (0..8).filter(|&m| v[8 * i + m] != M31::ZERO).collect();
        if !ls.is_empty() {
            out.push(format!("{}{:?}", bat_label(i), ls));
        }
    }
    out
}
/// Batched coordinate indices as compressed label ranges.
fn ranges(cs: &[usize]) -> String {
    let mut out = vec![];
    let mut i = 0;
    while i < cs.len() {
        let mut j = i;
        while j + 1 < cs.len() && cs[j + 1] == cs[j] + 1 {
            j += 1;
        }
        out.push(if i == j { bat_label(cs[i]) } else { format!("{}..{}", bat_label(cs[i]), bat_label(cs[j])) });
        i = j + 1;
    }
    format!("[{}]", out.join(","))
}
/// Ranks of a batched image projected to h, to f, and to the f-prefixes f[0..m).
fn projection_ranks(label: &str, kind: &str, img: &Ech<M31>) {
    let rows: Vec<Vec<M31>> = ech_rows(img);
    let h = rank_of(56, rows.iter().map(|r| r[8..64].to_vec()));
    let f = rank_of(2048, rows.iter().map(|r| r[64..].to_vec()));
    let pre: Vec<(usize, usize)> = [1usize, 2, 4, 8, 12, 13, 14, 15, 16, 20, 24, 32, 64, 128, 256]
        .iter()
        .map(|&m| (m, rank_of(8 * m, rows.iter().map(|r| r[64..64 + 8 * m].to_vec()))))
        .collect();
    println!("Z8C_PROJ {label} kind={kind} rank={} h_rank={h} f_rank={f} f_prefix_ranks={pre:?}", img.rank);
}
/// Left kernel of a batched image (Ech over BW limbs): which candidate
/// relations annihilate it, how much of the annihilator they explain, and the
/// supports of an echelon basis of the unexplained remainder.
fn left_kernel_report(label: &str, kind: &str, img: &Ech<M31>, cands: &[&Rel]) {
    let rows: Vec<Vec<W>> = img.p.iter().flatten().map(|r| wvals(r)).collect();
    let ann = BW - img.rank;
    let mut holds = vec![];
    let mut fails = vec![];
    let mut expl = Ech::new(BW);
    for c in cands {
        if rows.iter().all(|y| c.eval(y) == W::ZERO) {
            holds.push(c.name.clone());
            for f in c.limb_functionals() {
                expl.insert(f);
            }
        } else {
            let bad = rows.iter().filter(|y| c.eval(y) != W::ZERO).count();
            fails.push(format!("{}({bad})", c.name));
        }
    }
    println!(
        "Z8C_LEFT_KERNEL {label} kind={kind} image_rank={} annihilator_dim={ann} candidates={} holding={} failing={} explained_dim={} unexplained_dim={} failing_names={fails:?}",
        img.rank,
        cands.len(),
        holds.len(),
        fails.len(),
        expl.rank,
        ann - expl.rank
    );
    if expl.rank < ann {
        let mut rest = Ech::new(BW);
        let mut rest_rows = vec![];
        for nv in null_space(img) {
            let r = expl.residual(nv);
            if r.iter().any(|x| *x != M31::ZERO) {
                if rest.insert(r.clone()).is_some() {
                    rest_rows.push(r);
                }
            }
        }
        // Fully reduce the remainder basis (back-substitution) and print
        // supports as batched-coordinate ranges.
        let mut piv: Vec<usize> = rest_rows.iter().map(|r| r.iter().position(|x| *x != M31::ZERO).unwrap()).collect();
        let mut order: Vec<usize> = (0..rest_rows.len()).collect();
        order.sort_by_key(|&i| piv[i]);
        rest_rows = order.iter().map(|&i| rest_rows[i].clone()).collect();
        piv = order.iter().map(|&i| piv[i]).collect();
        for i in (0..rest_rows.len()).rev() {
            let ri = rest_rows[i].clone();
            for j in 0..rest_rows.len() {
                if j != i && rest_rows[j][piv[i]] != M31::ZERO {
                    let sc = rest_rows[j][piv[i]];
                    for t in 0..BW {
                        rest_rows[j][t] = rest_rows[j][t].sub(sc.mul(ri[t]));
                    }
                }
            }
        }
        let mut union = std::collections::BTreeSet::new();
        for (n, r) in rest_rows.iter().enumerate() {
            let cs: Vec<usize> = (0..NB).filter(|&i| (0..8).any(|m| r[8 * i + m] != M31::ZERO)).collect();
            union.extend(cs.iter().copied());
            if n < 16 || n + 4 >= rest_rows.len() {
                println!(
                    "Z8C_LEFT_KERNEL_REST {label} kind={kind} index={n} pivot={}:{} support={}",
                    bat_label(piv[n] / 8),
                    piv[n] % 8,
                    ranges(&cs)
                );
            }
        }
        let _ = support_labels;
        println!("Z8C_LEFT_KERNEL_REST_UNION {label} kind={kind} rank={} support={}", rest.rank, ranges(&union.into_iter().collect::<Vec<_>>()));
    }
}
/// Ech whose pivot order is the round-j coefficients from degree 27 down to
/// 0, all four limbs per degree; returns pivot degrees (one entry per limb pivot).
fn leading_degrees(polys: &[[QM31; 28]]) -> Vec<usize> {
    let mut e = Ech::new(112);
    for p in polys {
        let v: Vec<M31> = (0..28).rev().flat_map(|d| limbs(p[d])).collect();
        e.insert(v);
    }
    (0..112).filter(|&i| e.p[i].is_some()).map(|i| 27 - i / 4).collect()
}

pub(super) fn main() {
    let args: Vec<_> = std::env::args().collect();
    let get = |k: &str| args.windows(2).find(|x| x[0] == k).map(|x| x[1].clone());
    let s = get("--structure").expect("--structure");
    let v: usize = get("--vector").expect("--vector").parse().unwrap();
    let preflight = args.iter().any(|x| x == "--preflight");
    let start = Instant::now();
    println!("Z8C_START structure={s} vector={v} preflight={preflight} transport=D13 batching=WideExact balanced=true proxy=false");
    let t = trial(v);
    let a = alpha_for(&s, v, &t.a);
    let label = format!("structure={s} vector={v}");
    let op = opening_challenges(v);
    println!(
        "Z8C_ALPHA {label} alpha={:?} lambda_dims={:?} good3={} outside_k2={:?}",
        a.map(l4),
        lambda_dims(&a),
        good3(&a),
        (0..10).map(|i| !in_k2(a[i]) as u8).collect::<Vec<_>>()
    );
    println!(
        "Z8C_OPENING {label} gamma={:?} kappa={:?} tau={:?} fold={:?}",
        op.gamma.to_limbs(),
        op.kappa.to_limbs(),
        op.tau.to_limbs(),
        op.fold.to_limbs()
    );
    let basis = NaturalBasis::new(BasisSize::Initial).expect("basis");
    let z = [wpt(t.z[0]), wpt(t.z[1])];
    let total = total_weights(&basis, &a, z, &op);
    let phi = unit_functionals(&basis, z, &total, &op);
    println!("Z8C_CHECK unit_quotients=1024 ok=true eq_orientation=true seconds={:.3}", start.elapsed().as_secs_f64());
    let beta: Vec<[W; NB]> = (0..N)
        .map(|r| {
            let mut b = [W::ZERO; NB];
            b[0] = if inactive(r) { W::ONE } else { W::ZERO };
            b[1..].copy_from_slice(&phi[usize::from(ROW_TO_COEFFICIENT[r])]);
            b
        })
        .collect();
    let gpow = (0..29).map(|l| op.gamma.pow(l as u64)).collect();
    let (br, gr) = raw_c(&a, &t.z, &t.qs);
    let tail: Vec<_> = (0..N).map(|r| tail_row(&a, r)).collect();
    let cx = Ctx { a, br, gr, tail, beta, gpow };
    decomposition_check(&cx, &basis, z, &total, &op, 0x5a38_c0de ^ v as u64);
    // Transport / layout facts used below.
    assert!(inactive(0), "row 0 must be copy-inactive (balance 0)");
    for r in 0..N {
        assert_eq!(usize::from(ROW_TO_COEFFICIENT[r]), usize::from(z5::transport()[r]), "transport tables agree");
    }
    let rows_lo: Vec<usize> = (0..56).map(|k| usize::from(COEFFICIENT_TO_ROW[k])).collect();
    let rows_hi: Vec<usize> = (56..1024).map(|k| usize::from(COEFFICIENT_TO_ROW[k])).collect();
    let n_inactive = (0..N).filter(|&r| inactive(r)).count();
    println!(
        "Z8C_LAYOUT {label} inactive_rows={n_inactive} row0_coefficient={} rows_lo_all_inactive={} row0_in_rows_lo={} coeff_lt_89_all_inactive={}",
        ROW_TO_COEFFICIENT[0],
        rows_lo.iter().all(|&r| inactive(r)),
        rows_lo.contains(&0),
        (0..89).all(|k| inactive(usize::from(COEFFICIENT_TO_ROW[k])))
    );
    let rel = relations(&total, &op, &t.qs);
    let ln = Lanes::new(&cx);
    println!("Z8C_SETUP {label} seconds={:.3}", start.elapsed().as_secs_f64());

    // ---- Pass 1: per-lane own kernels, carrying [batched | round]; global gate Ech. ----
    let mut pure = Ech::new(TW);
    let mut rker: Vec<Ech<M31>> = vec![];
    let mut own_rank = vec![];
    let mut kernel_dims = vec![];
    let mut rel_viol = [0usize; 4]; // ia, S1, S2, S3 (any u)
    let mut carries_checked = 0usize;
    for li in 0..LANES {
        let mut rk = Ech::new(RW);
        let mut ker = 0;
        let n = ln.count(li);
        lane_kernel(
            n,
            |i| {
                let (o, b, r) = ln.bal(li, i);
                (o, carry(b, &r))
            },
            |c| {
                ker += 1;
                let y = wvals(&c[..BW]);
                carries_checked += 1;
                if y[0] != W::ZERO {
                    rel_viol[0] += 1;
                }
                if rel.s1.eval(&y) != W::ZERO {
                    rel_viol[1] += 1;
                }
                if rel.s2.eval(&y) != W::ZERO {
                    rel_viol[2] += 1;
                }
                if rel.s3.iter().any(|r| r.eval(&y) != W::ZERO) {
                    rel_viol[3] += 1;
                }
                rk.insert(c[BW..].to_vec());
                pure.insert(c);
            },
        );
        own_rank.push(n - ker);
        kernel_dims.push(ker);
        println!(
            "Z8C_LANE_OWN {label} lane={} sources={n} own_rank={} own_functionals={} round_image_of_own_kernel={} seconds={:.3}",
            lane_name(li),
            n - ker,
            own_width(li),
            rk.rank,
            start.elapsed().as_secs_f64()
        );
        rker.push(rk);
    }
    let ia_pivots = (0..8).filter(|&i| pure.p[i].is_some()).count();
    let batched_rank = (0..BW).filter(|&i| pure.p[i].is_some()).count();
    println!(
        "Z8C_RELATIONS {label} carries_checked={carries_checked} violations_ia={} violations_S1={} violations_S2={} violations_S3={} relations_annihilate_exactly={}",
        rel_viol[0],
        rel_viol[1],
        rel_viol[2],
        rel_viol[3],
        rel_viol.iter().all(|x| *x == 0)
    );
    if rel_viol.iter().any(|x| *x != 0) {
        println!("STOP reason=verifier_relation_not_annihilating {label} violations={rel_viol:?}");
    }
    let retained = slice_image(&pure, BW);
    let silent = slice_image(&pure, BW + 4);
    // (2) dim R(ker own) = sum of per-lane own-kernel round images.
    let mut rown = Ech::new(RW);
    for rk in &rker {
        for row in ech_rows(rk) {
            rown.insert(row);
        }
    }
    let rown_zero = initial_zero(copied_ech(&rown));
    println!(
        "Z8C_GATE_PURE {label} span_rank={} batched_pivots={batched_rank} ia_pivots={ia_pivots} initial_retained_rank={} silent_rank={} upper_bound=1076 seconds={:.3}",
        pure.rank,
        retained.rank,
        silent.rank,
        start.elapsed().as_secs_f64()
    );
    println!(
        "Z8C_QPRIME {label} round_image_of_ker_own_initial_retained={} initial_zero={} expect=1080",
        rown.rank, rown_zero.rank
    );
    println!(
        "Z8C_B {label} bat_rank_on_ker_own={} bat_rank_on_ker_own_and_ker_R={} expect=1912 (second = span_rank - dim R(ker own) = {} - {})",
        batched_rank - ia_pivots,
        pure.rank - rown.rank,
        pure.rank,
        rown.rank
    );
    let psil = Proj::of(&silent, &a);
    report(&label, "silent", silent.rank, &psil);
    report(&label, "silent_initial_retained", retained.rank, &Proj::of(&retained, &a));
    report(&label, "round_image_of_ker_own", rown.rank, &Proj::of(&rown, &a));
    if silent.rank < 1076 {
        println!("Z8C_FINDING {label} balanced_silent_rank={} below=1076 deficit={}", silent.rank, 1076 - silent.rank);
    }
    let chain0: Vec<Vec<M31>> = (4..RW)
        .map(|i| {
            let mut u = vec![M31::ZERO; RW];
            u[i] = M31::ONE;
            let q = unflat(&u);
            let phi = final_value(&q, &a);
            flatten(&normalize_d(&q, phi, &a).expect("alpha9=1/2"))
        })
        .collect();
    summarize(&format!("{label} chain0_basis"), &silent, &chain0);
    summarize(&format!("{label} qprime_chain0_basis"), &rown_zero, &chain0);
    // (5a) left kernel of bat on ker own.
    {
        let mut img = Ech::new(BW);
        for row in pure.p.iter().take(BW).flatten() {
            img.insert(row[..BW].to_vec());
        }
        let mut c: Vec<&Rel> = vec![&rel.ia, &rel.s1, &rel.s2];
        c.extend(rel.s3.iter());
        left_kernel_report(&label, "bat_on_ker_own", &img, &c);
    }
    println!("Z8C_PASS1_DONE {label} seconds={:.3}", start.elapsed().as_secs_f64());

    // ---- Pass 2: per lane, rounds first: rank R_l, own on ker R_l (OT_l). ----
    let mut rall = Ech::new(RW);
    for li in 0..LANES {
        let mut ker = vec![];
        let piv = lane_elim(
            ln.count(li),
            |i| {
                let (o, _, r) = ln.bal(li, i);
                (flatten(&r), o)
            },
            |c| ker.push(c),
        );
        for p in &piv {
            rall.insert(p.clone());
        }
        println!(
            "Z8C_LANE_OT {label} lane={} rank_R={} ker_R_dim={} own_on_ker_R=[{}]",
            lane_name(li),
            piv.len(),
            ker.len(),
            fmt_ranks(&block_ranks(li, &ker))
        );
    }
    println!("Z8C_R_ALL {label} rank_R_M_bal={} initial_zero={} expect=1084", rall.rank, initial_zero(copied_ech(&rall)).rank);
    // F5: claim_2 on ker R_{l,6} (full round-6 polynomial).
    for li in 0..LANES {
        let mut ker = vec![];
        lane_elim(
            ln.count(li),
            |i| {
                let (o, _, r) = ln.bal(li, i);
                (flatten(&round_polys(&r, &a)[6]), o[8..12].to_vec())
            },
            |c| ker.push(c),
        );
        println!(
            "Z8C_F5 {label} lane={} claim2_rank_on_ker_R6={} claim2_in_rowspace_R6={}",
            lane_name(li),
            rank_of(4, ker.iter().cloned()),
            rank_of(4, ker.iter().cloned()) == 0
        );
    }
    // OT': own on R_l^{-1}(V_{!=l}), V_{!=l} = sum of the other lanes' own-kernel round images.
    {
        let bases: Vec<Vec<Vec<M31>>> = rker.iter().map(ech_rows).collect();
        let mut prefix = vec![Ech::new(RW)];
        for li in 0..LANES {
            let mut e = copied_ech(&prefix[li]);
            for b in &bases[li] {
                e.insert(b.clone());
            }
            prefix.push(e);
        }
        let mut suffix = vec![Ech::new(RW)];
        for li in (0..LANES).rev() {
            let mut e = copied_ech(suffix.last().unwrap());
            for b in &bases[li] {
                e.insert(b.clone());
            }
            suffix.push(e);
        }
        suffix.reverse(); // suffix[i] = lanes i..
        for li in 0..LANES {
            let mut vne = copied_ech(&prefix[li]);
            for b in ech_rows(&suffix[li + 1]) {
                vne.insert(b);
            }
            let mut ker = vec![];
            lane_elim(
                ln.count(li),
                |i| {
                    let (o, _, r) = ln.bal(li, i);
                    (vne.residual(flatten(&r)), o)
                },
                |c| ker.push(c),
            );
            println!(
                "Z8C_LANE_OTPRIME {label} lane={} dim_V_other={} preimage_dim={} own_on_preimage=[{}]",
                lane_name(li),
                vne.rank,
                ker.len(),
                fmt_ranks(&block_ranks(li, &ker))
            );
        }
    }
    println!("Z8C_PASS2_DONE {label} seconds={:.3}", start.elapsed().as_secs_f64());

    // ---- (5b) D-high_bal, and Z8b's unbalanced (P) block. ----
    let mut dhigh_img: Option<Ech<M31>> = None;
    {
        let s0 = *rows_hi.iter().find(|&&r| inactive(r)).expect("an inactive D-high row");
        for &r in &rows_hi {
            assert!(ln.rr[11][r].iter().all(|x| *x == QM31::ZERO), "D coefficient >= 56 has a round contribution");
        }
        let mut srcs: Vec<(usize, usize, bool)> = vec![]; // (row, limb, subtract s0)
        for &r in &rows_hi {
            if r == s0 {
                continue;
            }
            for k in 0..4 {
                srcs.push((r, k, inactive(r)));
            }
        }
        let mut cands: Vec<&Rel> = vec![&rel.ia, &rel.s1, &rel.s2];
        cands.extend(rel.s3.iter());
        cands.extend(rel.low.iter());
        let mut img = Ech::new(BW);
        let own_piv = lane_elim(
            srcs.len(),
            |i| {
                let (r, k, sub) = srcs[i];
                let (o, b, _) = ln.raw(11, r, k);
                if sub {
                    let (o0, b0, _) = ln.raw(11, s0, k);
                    (sub_vec(&o, &o0, |x, y| x.sub(y)), wflat(&sub_vec(&b, &b0, |x, y| x.sub(y))))
                } else {
                    (o, wflat(&b))
                }
            },
            |c| {
                img.insert(c);
            },
        );
        println!(
            "Z8C_DHIGH_BAL {label} sources={} base_row={s0} own_rank={} bat_rank_on_ker_own_D={} expect=1800 ia_pivots={}",
            srcs.len(),
            own_piv.len(),
            img.rank,
            (0..8).filter(|&i| img.p[i].is_some()).count()
        );
        projection_ranks(&label, "dhigh_bal", &img);
        left_kernel_report(&label, "dhigh_bal", &img, &cands);
        dhigh_img = Some(img);
        // Z8b (P) block, unbalanced: every D row with coefficient >= 56.
        let mut up = Ech::new(BW);
        let own_up = lane_elim(
            rows_hi.len() * 4,
            |i| {
                let (o, b, _) = ln.raw(11, rows_hi[i / 4], i % 4);
                (o, wflat(&b))
            },
            |c| {
                up.insert(c);
            },
        );
        println!(
            "Z8C_DHIGH_UNBAL {label} sources={} own_rank={} bat_rank_on_ker_own_D={} z8b=1812 ia_pivots={}",
            rows_hi.len() * 4,
            own_up.len(),
            up.rank,
            (0..8).filter(|&i| up.p[i].is_some()).count()
        );
        let mut cu: Vec<&Rel> = vec![&rel.ia, &rel.s1, &rel.s2, &rel.s2u];
        cu.extend(rel.s3.iter());
        cu.extend(rel.low.iter());
        projection_ranks(&label, "dhigh_unbal_z8b_P", &up);
        left_kernel_report(&label, "dhigh_unbal_z8b_P", &up, &cu);
    }
    println!("Z8C_PASS5_DONE {label} seconds={:.3}", start.elapsed().as_secs_f64());

    // ---- (6) G-low: restriction of ker R_G ∩ ker own_G to rows pi^-1(0..55), and the low folds;
    // variant without G's extra claim; assembly of (B) from D-high_bal and G (ker R_G ∩ ker own_G). ----
    for (variant, drop_extra) in [("own_all", false), ("own_without_extra", true)] {
        let mut ker = vec![];
        lane_elim(
            ln.count(10),
            |i| {
                let (r, k) = ln.row_of(10, i);
                let (o, b, rd) = ln.bal(10, i);
                let mut vv: Vec<M31> = if drop_extra { o[..12].iter().chain(&o[16..]).copied().collect() } else { o };
                vv.extend(flatten(&rd));
                let x = tower(k);
                let mut c = vec![];
                for &lr in &rows_lo {
                    let mut val = QM31::ZERO;
                    if lr == r {
                        val = val.add(x);
                    }
                    if lr == 0 && inactive(r) {
                        val = val.sub(x);
                    }
                    c.extend(limbs(val));
                }
                c.extend(wflat(&b));
                (vv, c)
            },
            |c| ker.push(c),
        );
        let assembled = if drop_extra {
            String::new()
        } else {
            let mut e = copied_ech(dhigh_img.as_ref().unwrap());
            for c in &ker {
                e.insert(c[224..].to_vec());
            }
            let mut gonly = Ech::new(BW);
            for c in &ker {
                gonly.insert(c[224..].to_vec());
            }
            projection_ranks(&label, "glow_bat", &gonly);
            format!(" g_bat_rank={} dhigh_plus_g_bat_rank={} expect_bat_on_ker_own={}", gonly.rank, e.rank, batched_rank - ia_pivots)
        };
        println!(
            "Z8C_GLOW {label} variant={variant} kernel_dim={} low_rows_rank={} expect=224 low_fold_rank={} expect=112 joint_rank={}{assembled}",
            ker.len(),
            rank_of(224, ker.iter().map(|c| c[..224].to_vec())),
            rank_of(112, ker.iter().map(|c| c[224 + 64..224 + 64 + 112].to_vec())),
            rank_of(336, ker.iter().map(|c| c[..224 + 64 + 112].iter().enumerate().filter(|(j, _)| *j < 224 || *j >= 288).map(|(_, x)| *x).collect()))
        );
    }

    // ---- (7) PR6 / PR7 on G (unbalanced words in one prefix block; local statements). ----
    {
        let block6: Vec<usize> = (16..32).collect(); // prefix l' = 1 (6 bits), suffix s in {0,1}^4
        let block7: Vec<usize> = (16..24).collect(); // prefix l' = 2 (7 bits), suffix s in {0,1}^3
        let polys = |r: usize, k: usize| round_polys(&scale(&ln.rr[10][r], tower(k)), &a);
        let claim = |r: usize, k: usize, j: usize| flatten(&[cx.gr[r][1 + j].mul(tower(k))]);
        // Fresh-at-6 (rounds 7..9 zero): round-6 leading degrees, and deg <= 22 part with claim_2.
        let mut fresh = vec![];
        lane_kernel(
            64,
            |i| {
                let (r, k) = (block6[i / 4], i % 4);
                let p = polys(r, k);
                let v: Vec<M31> = (7..10).flat_map(|j| flatten(&p[j])).collect();
                let mut c = flatten(&p[6]);
                c.extend(claim(r, k, 2));
                (v, c)
            },
            |c| fresh.push(c),
        );
        let fresh_polys: Vec<[QM31; 28]> = fresh.iter().map(|c| std::array::from_fn(|d| unflat(&c[4 * d..4 * d + 4])[0])).collect();
        let mut low6 = vec![];
        lane_kernel(
            fresh.len(),
            |i| {
                let c = &fresh[i];
                (c[4 * 23..112].to_vec(), c[112..116].to_vec())
            },
            |c| low6.push(c),
        );
        println!(
            "Z8C_PR6 {label} fresh6_dim={} round6_leading_degrees={:?} deg_le_22_dim={} claim2_rank_on_deg_le_22={} pr6_holds={}",
            fresh.len(),
            leading_degrees(&fresh_polys),
            low6.len(),
            rank_of(4, low6.iter().cloned()),
            rank_of(4, low6.iter().cloned()) > 0
        );
        let mut all7 = vec![];
        let mut src7 = vec![];
        for i in 0..32 {
            let (r, k) = (block7[i / 4], i % 4);
            let p = polys(r, k);
            all7.push(p[7]);
            let mut c = flatten(&p[7]);
            c.extend(claim(r, k, 0));
            src7.push(c);
        }
        let mut low7 = vec![];
        lane_kernel(32, |i| (src7[i][4 * 23..112].to_vec(), src7[i][112..116].to_vec()), |c| low7.push(c));
        println!(
            "Z8C_PR7 {label} round7_dim={} round7_leading_degrees={:?} deg_le_22_dim={} claim0_rank_on_deg_le_22={} pr7_holds={}",
            rank_of(112, all7.iter().map(|p| flatten(p))),
            leading_degrees(&all7),
            low7.len(),
            rank_of(4, low7.iter().cloned()),
            rank_of(4, low7.iter().cloned()) > 0
        );
    }
    println!("Z8C_ITEMS_DONE {label} seconds={:.3}", start.elapsed().as_secs_f64());
    if preflight {
        println!("Z8C_PREFLIGHT_DONE {label} wall_seconds={:.3}", start.elapsed().as_secs_f64());
        return;
    }
    // ---- (i') and (ii') as Z8 (copied from z8.rs main, tags renamed). ----
    let (pubdata, instances) = real::instances();
    let ch = t.ch;
    let traces: Vec<Trace> = instances
        .iter()
        .map(|w| {
            let mut tr: Trace = w
                .compilation
                .semantic_c1
                .c1
                .iter()
                .map(|col| col.iter().map(|x| QM31::from_m31(*x)).collect())
                .collect();
            match build_pool_v1_pair_forest_copy_helper_v1(
                &w.compilation.trace,
                w.compilation.public_statement.live_snapshot.next_pair_index,
                ch.lambda,
                ch.chi,
            ) {
                Ok(h) => tr.push(h),
                Err(error) => {
                    println!("STOP reason=helper_pole_or_helper_abort {label} error={error:?}");
                    std::process::exit(22);
                }
            }
            balance_trace(&mut tr);
            tr
        })
        .collect();
    let mut targets = vec![];
    for pair in 0..5 {
        let mut noise = t.tapes[pair].clone();
        balance_trace(&mut noise);
        let public = Public::Transfer(&pubdata, &instances[2 * pair].compilation.public_statement);
        let original = compute_targets(public, &a, &ch, &traces[2 * pair], &traces[2 * pair + 1], &noise, pair);
        println!(
            "Z8C_TERMINAL {label} pair={pair} pinned={:?} derivative={:?} ii={:?}",
            l4(original.terminal[0]),
            l4(original.terminal[1]),
            l4(original.terminal[2])
        );
        targets.push(normalized(&original, &a, &traces[2 * pair], &traces[2 * pair + 1], &ch, public));
    }
    let i: Vec<_> = targets.iter().map(|t| flatten(&t.pinned)).collect();
    let derivative: Vec<_> = targets.iter().map(|t| flatten(&t.derivative)).collect();
    summarize(&format!("{label} wide_i_prime"), &silent, &i);
    summarize(&format!("{label} wide_derivative_diagnostic"), &silent, &derivative);
    let mut full = Ech { p: pure.p.clone(), rank: pure.rank };
    let sol = conditioned_sources(&cx, &traces, 5, &mut full);
    let conditioned = slice_image(&full, BW);
    let mut ii = vec![];
    let mut batched_unmatched = vec![];
    for p in 0..5 {
        let mut b = vec![W::ZERO; NB];
        for c in 0..17 {
            let lane = if c == 16 { 26 } else { c };
            for r in 0..N {
                let d = traces[2 * p][c][r].sub(traces[2 * p + 1][c][r]);
                if d == QM31::ZERO {
                    continue;
                }
                for (e, x) in b.iter_mut().zip(cx.batched(lane, wq(d), r)) {
                    *e = e.add(x);
                }
            }
        }
        let target = carry(b, &targets[p].difference);
        let residual = batched_reduce(&full, sub_vec(&target, &sol[p], |x, y| x.sub(y)));
        let unmatched = residual[..BW].iter().filter(|x| **x != M31::ZERO).count();
        batched_unmatched.push(unmatched);
        ii.push(residual[BW..].to_vec());
    }
    println!("Z8C_II_BATCHED {label} batched_coordinates_unmatched_per_pair={batched_unmatched:?}");
    summarize(&format!("{label} wide_ii_prime"), &conditioned, &ii);
    let ip = pass_count(&silent, &i);
    let iip = (0..5).filter(|&p| batched_unmatched[p] == 0 && conditioned.residual(ii[p].clone()).iter().all(|x| *x == M31::ZERO)).count();
    println!(
        "Z8C_GATE {label} silent_rank={} initial_retained_rank={} full_span_rank={} full_conditioned_rank={} i_pass={ip} ii_pass={iip} attempted=5",
        silent.rank,
        retained.rank,
        full.rank,
        conditioned.rank
    );
    println!("Z8C_DONE {label} wall_seconds={:.3}", start.elapsed().as_secs_f64());
}
