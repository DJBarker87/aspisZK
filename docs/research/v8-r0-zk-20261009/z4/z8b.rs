//! Z8b (LOG D20‴.3 "Z8b"): numeric check of the PCS-cancellation /
//! round-spanning decomposition on Z8's structure-(A) vectors, with Z8's
//! WideExact batching and real linearPayload silence coordinates.
//!
//! Everything above `// ---- Z8b ----` is copied verbatim from z8.rs (trial
//! replay, alpha helpers, round_polys, Proj, WideExact opening challenges,
//! Lean totalWeights, column-wise unit quotient functionals, Ctx, carry,
//! scale, report, decomposition_check). Rank routines: probe.rs's Ech,
//! initial_zero, copied_ech, summarize, pass_count (unchanged).
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

fn carry(batched: Vec<W>, round: &[QM31]) -> Vec<M31> {
    let mut c = wflat(&batched);
    c.extend(flatten(round));
    debug_assert_eq!(c.len(), TW);
    c
}
fn scale(v: &[QM31], x: QM31) -> Vec<QM31> {
    v.iter().map(|y| y.mul(x)).collect()
}
fn report(label: &str, kind: &str, total: usize, p: &Proj) {
    println!(
        "Z8B_RANKS {label} kind={kind} total={total} round_full={:?} round_limb={:?}",
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
    println!("Z8B_CHECK decomposition lanes=[16,27,28] whole_column_pipeline_equals_rowwise_sum=true coordinates={NB}");
}


// ---- Z8b ----
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

pub(super) fn main() {
    let args: Vec<_> = std::env::args().collect();
    let get = |k: &str| args.windows(2).find(|x| x[0] == k).map(|x| x[1].clone());
    let s = get("--structure").unwrap_or_else(|| "A".to_string());
    let v: usize = get("--vector").expect("--vector").parse().unwrap();
    let preflight = args.iter().any(|x| x == "--preflight");
    let start = Instant::now();
    println!("Z8B_START structure={s} vector={v} preflight={preflight} transport=D13 batching=WideExact");
    let t = trial(v);
    let a = alpha_for(&s, v, &t.a);
    let label = format!("structure={s} vector={v}");
    let op = opening_challenges(v);
    println!("Z8B_ALPHA {label} alpha={:?} lambda_dims={:?}", a.map(l4), lambda_dims(&a));
    println!(
        "Z8B_OPENING {label} gamma={:?} kappa={:?} tau={:?} fold={:?}",
        op.gamma.to_limbs(),
        op.kappa.to_limbs(),
        op.tau.to_limbs(),
        op.fold.to_limbs()
    );
    let basis = NaturalBasis::new(BasisSize::Initial).expect("basis");
    let z = [wpt(t.z[0]), wpt(t.z[1])];
    let total = total_weights(&basis, &a, z, &op);
    let phi = unit_functionals(&basis, z, &total, &op);
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
    let rows_lo: Vec<usize> = (0..56).map(|k| usize::from(COEFFICIENT_TO_ROW[k])).collect();
    let rows_hi: Vec<usize> = (56..1024).map(|k| usize::from(COEFFICIENT_TO_ROW[k])).collect();
    for &r in &rows_hi {
        assert!(cx.tail[r].iter().all(|x| *x == QM31::ZERO), "D coefficient >= 56 has a round contribution");
    }
    let xs: Vec<QM31> = (0..4).map(tower).collect();

    // Per-lane own-silence functional ranks (rows = all 1,024 sources).
    let mask_ranks: Vec<usize> = (0..10).map(|_| rank_of(112, (0..N).map(|r| cx.br[r][1..].to_vec()))).collect();
    let k4_rank = rank_of(DW, (0..N).flat_map(|r| xs.iter().map(move |&x| (r, x))).map(|(r, x)| d_own(&cx, r, x)));
    let g_inactive_rank = rank_of(DW + 4, (0..N).flat_map(|r| xs.iter().map(move |&x| (r, x))).map(|(r, x)| g_lane_coords(&cx, r, x, true)));
    let d_lo_rank = rank_of(DW, rows_lo.iter().flat_map(|&r| xs.iter().map(move |&x| (r, x))).map(|(r, x)| d_own(&cx, r, x)));
    let d_hi_rank = rank_of(DW, rows_hi.iter().flat_map(|&r| xs.iter().map(move |&x| (r, x))).map(|(r, x)| d_own(&cx, r, x)));
    println!(
        "Z8B_LANE_RANKS {label} mask_only={mask_ranks:?} mask_functionals=112 G={k4_rank} D={k4_rank} k4_functionals={DW} G_with_inactive_sum={g_inactive_rank} of={} D_coeff_0_55={d_lo_rank} D_coeff_56_1023={d_hi_rank}",
        DW + 4
    );

    // (1) PCS cancellation block: batched (2,112) + D own (376) on D's coefficients 56..1023.
    let hi_gens: Vec<Vec<M31>> = rows_hi
        .iter()
        .flat_map(|&r| xs.iter().map(move |&x| (r, x)))
        .map(|(r, x)| {
            let mut g = wflat(&cx.batched(28, wq(x), r));
            g.extend(d_own(&cx, r, x));
            g
        })
        .collect();
    let g_inact: Vec<Vec<M31>> = xs
        .iter()
        .map(|&x| {
            let mut b = vec![W::ZERO; NB];
            b[0] = cx.gpow[27].mul(wq(x));
            let mut g = wflat(&b);
            g.extend(vec![M31::ZERO; DW]);
            g
        })
        .collect();
    let block = |gs: &[Vec<M31>]| {
        (
            rank_of(BW + DW, gs.iter().cloned()),
            rank_of(BW, gs.iter().map(|g| g[..BW].to_vec())),
            rank_of(DW, gs.iter().map(|g| g[BW..].to_vec())),
            rank_of(8, gs.iter().map(|g| g[..8].to_vec())),
            rank_of(BW - 8, gs.iter().map(|g| g[8..BW].to_vec())),
        )
    };
    let (r1, rb, rd, ri, ro) = block(&hi_gens);
    println!("Z8B_P1 {label} variant=D_56_1023 columns={} rank={r1} batched_only={rb} d_own_only={rd} inactive_sum_only={ri} opening_final_only={ro} functionals={}", hi_gens.len(), BW + DW);
    let mut with_g = hi_gens.clone();
    with_g.extend(g_inact);
    let (r1g, rbg, rdg, rig, rog) = block(&with_g);
    println!("Z8B_P1 {label} variant=D_56_1023_plus_G_inactive_sum columns={} rank={r1g} batched_only={rbg} d_own_only={rdg} inactive_sum_only={rig} opening_final_only={rog} functionals={}", with_g.len(), BW + DW);

    // (2) round spanning and (3) assembled silent subspace.
    let mut e2 = Ech::new(RW);
    let mut e3 = Ech::new(SW);
    let mut count = [0usize; 3];
    for c in 0..10 {
        let lane = 16 + c;
        lane_kernel(
            N,
            |r| (cx.br[r][1..].to_vec(), gen3(cx.batched(lane, W::ONE, r), vec![M31::ZERO; DW], &round_row(&a, r, c))),
            |g| {
                count[0] += 1;
                e2.insert(g[BW + DW..].to_vec());
                e3.insert(g);
            },
        );
    }
    lane_kernel(
        4 * N,
        |i| {
            let (r, x) = (i / 4, tower(i % 4));
            (g_lane_coords(&cx, r, x, true), gen3(cx.batched(27, wq(x), r), vec![M31::ZERO; DW], &scale(&round_row(&a, r, 10), x)))
        },
        |g| {
            count[1] += 1;
            e2.insert(g[BW + DW..].to_vec());
            e3.insert(g);
        },
    );
    for &r in &rows_lo {
        for &x in &xs {
            let g = gen3(cx.batched(28, wq(x), r), d_own(&cx, r, x), &scale(&cx.tail[r], x));
            count[2] += 1;
            e2.insert(g[BW + DW..].to_vec());
            e3.insert(g);
        }
    }
    let e2z = initial_zero(copied_ech(&e2));
    println!(
        "Z8B_Q2 {label} generators_mask_kernel={} generators_G_kernel={} generators_D_0_55={} round_rank_initial_retained={} round_rank_initial_zero={} seconds={:.3}",
        count[0], count[1], count[2], e2.rank, e2z.rank, start.elapsed().as_secs_f64()
    );
    report(&label, "q2_round_image_initial_retained", e2.rank, &Proj::of(&e2, &a));
    report(&label, "q2_round_image_initial_zero", e2z.rank, &Proj::of(&e2z, &a));
    let q2_silent = slice_from(&e3, BW + DW + 4, BW + DW, RW);
    println!("Z8B_Q2_SILENT {label} span_rank={} silent_rank_of_q2_generators_alone={}", e3.rank, q2_silent.rank);
    for g in &hi_gens {
        let mut v = g.clone();
        v.extend(vec![M31::ZERO; RW]);
        e3.insert(v);
    }
    let retained3 = slice_from(&e3, BW + DW, BW + DW, RW);
    let silent3 = slice_from(&e3, BW + DW + 4, BW + DW, RW);
    let silence_pivots = (0..BW + DW).filter(|&i| e3.p[i].is_some()).count();
    println!(
        "Z8B_ASSEMBLED {label} span_rank={} silence_pivots={silence_pivots} initial_retained_rank={} silent_rank={} z8_silent_rank=1076 seconds={:.3}",
        e3.rank, retained3.rank, silent3.rank, start.elapsed().as_secs_f64()
    );
    report(&label, "assembled_silent", silent3.rank, &Proj::of(&silent3, &a));
    report(&label, "assembled_silent_initial_retained", retained3.rank, &Proj::of(&retained3, &a));
    let chain0: Vec<Vec<M31>> = (4..RW)
        .map(|i| {
            let mut u = vec![M31::ZERO; RW];
            u[i] = M31::ONE;
            let q = unflat(&u);
            let phi = final_value(&q, &a);
            flatten(&normalize_d(&q, phi, &a).expect("alpha9=1/2"))
        })
        .collect();
    summarize(&format!("{label} q2_round_image_initial_zero_chain0"), &e2z, &chain0);
    summarize(&format!("{label} assembled_chain0_basis"), &silent3, &chain0);
    if preflight {
        println!("Z8B_PREFLIGHT_DONE {label} wall_seconds={:.3}", start.elapsed().as_secs_f64());
        return;
    }
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
            "Z8B_TERMINAL {label} pair={pair} pinned={:?} derivative={:?} ii={:?}",
            l4(original.terminal[0]),
            l4(original.terminal[1]),
            l4(original.terminal[2])
        );
        targets.push(normalized(&original, &a, &traces[2 * pair], &traces[2 * pair + 1], &ch, public));
    }
    let i: Vec<_> = targets.iter().map(|t| flatten(&t.pinned)).collect();
    let derivative: Vec<_> = targets.iter().map(|t| flatten(&t.derivative)).collect();
    summarize(&format!("{label} assembled_i_prime"), &silent3, &i);
    summarize(&format!("{label} assembled_derivative_diagnostic"), &silent3, &derivative);
    summarize(&format!("{label} q2_i_prime"), &e2z, &i);
    println!(
        "Z8B_GATE {label} assembled_silent_rank={} q2_round_rank_initial_zero={} i_pass_assembled={} i_pass_q2={} attempted=5",
        silent3.rank,
        e2z.rank,
        pass_count(&silent3, &i),
        pass_count(&e2z, &i)
    );
    println!("Z8B_DONE {label} wall_seconds={:.3}", start.elapsed().as_secs_f64());
}
