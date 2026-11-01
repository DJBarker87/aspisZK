//! Z8 (LOG D20′.2 / D20″ "Z8"): the silent-rank gate with the proved
//! protocol's WideExact-batched opening payload (R0Z/HonestView.lean
//! `linearPayload`, lines 191–220). Exact M31/QM31/WideExact arithmetic.
//!
//! Silence = every non-semantic payload coordinate is zero:
//!   per lane (Z4c's raw_c rows minus its per-lane inactive entry):
//!     .pointClaim j c (3), .extraClaim c, .ood j c (2), .opened q s c (88);
//!   batched over the 29 lanes with gamma = ch.opening 0 in WideExact:
//!     .inactiveSum   = sum_c gamma^c sum_{inactive rows} t_c,
//!     .openingCoeff i = coefficient i of relationLinear(openingWeights)(batch),
//!     .finalCoeff d   = foldLinear(ch.opening 3)(batch)[d],
//!   batch = sum_c gamma^c quotientLinear(z0,z1)(coeffs_pi(t_c)).
//! Each WideExact value is eliminated over M31 as its 8 canonical limbs.
//! No zero-batched-word proxy and no D-lift: D (lane 28) is an ordinary
//! K4-valued lane with its own word, observations and Libra round tail.
//!
//! Opening-layer functions are aspis-core's R0 code, applied column-wise to
//! coefficient unit vectors (all are linear): `prover::quotient` (chord
//! quotient, per lane with that lane's two OOD values), `chord::quotient_weights`
//! + `FunctionalWeights::{e1,e2}` (Lean `totalWeights`), `prover::round_polynomial`
//! (Lean `relationLinear`), `fold::fold_message` (Lean `foldLinear`). The Rust
//! `OpeningData::weights` omits Lean's `kappa^4 • extraWeight` (libraWeight);
//! it is added here so the weights equal Lean's `weights`.
//!
//! Reused from probe.rs unchanged: Ech (and residual), summarize, raw_c,
//! tail_row, round_row, eq, points, h_weight, compute_targets, normalized,
//! normalize_d, final_value, balance_trace, real::instances, eligible,
//! inactive. Copied: z6/z7 `trial`, z7's alpha helpers, `round_polys`, `Proj`.
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
const STRUCTURES: [&str; 4] = ["A", "B", "I", "J"];
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
fn alpha_for(s: &str, v: usize, base: &[QM31; 10]) -> [QM31; 10] {
    let si = STRUCTURES.iter().position(|x| *x == s).unwrap() as u64;
    let mut rng = Rng(STRUCT_SEED.wrapping_add((si * 64 + v as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15)));
    let mut a = *base;
    match s {
        "A" => {}
        "B" => (0..10).for_each(|i| a[i] = f_nontrivial(&mut rng, i == 9)),
        "I" => (0..10).for_each(|i| a[i] = k2_nontrivial(&mut rng, i == 9)),
        "J" => (1..7).for_each(|i| a[i] = f_nontrivial(&mut rng, false)),
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
        "Z8_RANKS {label} kind={kind} total={total} round_full={:?} round_limb={:?}",
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
    println!("Z8_CHECK decomposition lanes=[16,27,28] whole_column_pipeline_equals_rowwise_sum=true coordinates={NB}");
}

pub(super) fn main() {
    let args: Vec<_> = std::env::args().collect();
    let get = |k: &str| args.windows(2).find(|x| x[0] == k).map(|x| x[1].clone());
    let s = get("--structure").expect("--structure");
    let v: usize = get("--vector").expect("--vector").parse().unwrap();
    let preflight = args.iter().any(|x| x == "--preflight");
    let start = Instant::now();
    println!("Z8_START structure={s} vector={v} preflight={preflight} transport=D13 batching=WideExact dlift=false proxy=false");
    let t = trial(v);
    let a = alpha_for(&s, v, &t.a);
    let label = format!("structure={s} vector={v}");
    let op = opening_challenges(v);
    println!(
        "Z8_ALPHA {label} alpha={:?} lambda_dims={:?}",
        a.map(l4),
        lambda_dims(&a)
    );
    println!(
        "Z8_OPENING {label} gamma={:?} kappa={:?} tau={:?} fold={:?}",
        op.gamma.to_limbs(),
        op.kappa.to_limbs(),
        op.tau.to_limbs(),
        op.fold.to_limbs()
    );
    let basis = NaturalBasis::new(BasisSize::Initial).expect("basis");
    let z = [wpt(t.z[0]), wpt(t.z[1])];
    let total = total_weights(&basis, &a, z, &op);
    let phi = unit_functionals(&basis, z, &total, &op);
    println!("Z8_CHECK unit_quotients=1024 ok=true eq_orientation=true seconds={:.3}", start.elapsed().as_secs_f64());
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

    let mut pure = Ech::new(TW);
    pure_sources(&cx, &mut pure);
    let batched_rank = (0..BW).filter(|&i| pure.p[i].is_some()).count();
    let retained = slice_image(&pure, BW);
    let silent = slice_image(&pure, BW + 4);
    println!(
        "Z8_PURE {label} span_rank={} batched_pivots={batched_rank} initial_retained_rank={} silent_rank={} upper_bound=1076 seconds={:.3}",
        pure.rank,
        retained.rank,
        silent.rank,
        start.elapsed().as_secs_f64()
    );
    report(&label, "silent", silent.rank, &Proj::of(&silent, &a));
    report(&label, "silent_initial_retained", retained.rank, &Proj::of(&retained, &a));
    if s == "A" && silent.rank < 1076 {
        println!("Z8_FINDING {label} structure_A_silent_rank={} below=1076", silent.rank);
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
    if preflight {
        println!("Z8_PREFLIGHT_DONE {label} wall_seconds={:.3}", start.elapsed().as_secs_f64());
        return;
    }
    // Z4c's honest targets at this alpha.
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
            "Z8_TERMINAL {label} pair={pair} pinned={:?} derivative={:?} ii={:?}",
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
    // (ii'): witness-difference payload (per-lane + WideExact-batched) and rounds.
    let mut full = Ech { p: pure.p.clone(), rank: pure.rank };
    let sol = conditioned_sources(&cx, &traces, 5, &mut full);
    let conditioned = slice_image(&full, BW);
    let mut ii = vec![];
    let mut batched_unmatched = vec![];
    for p in 0..5 {
        // Witness difference's batched payload over semantic lanes 0..15 and H1 (lane 26).
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
    println!("Z8_II_BATCHED {label} batched_coordinates_unmatched_per_pair={batched_unmatched:?}");
    summarize(&format!("{label} wide_ii_prime"), &conditioned, &ii);
    let ip = pass_count(&silent, &i);
    let iip = (0..5).filter(|&p| batched_unmatched[p] == 0 && conditioned.residual(ii[p].clone()).iter().all(|x| *x == M31::ZERO)).count();
    println!(
        "Z8_GATE {label} silent_rank={} initial_retained_rank={} full_span_rank={} full_conditioned_rank={} i_pass={ip} ii_pass={iip} attempted=5",
        silent.rank,
        retained.rank,
        full.rank,
        conditioned.rank
    );
    println!("Z8_DONE {label} wall_seconds={:.3}", start.elapsed().as_secs_f64());
}
