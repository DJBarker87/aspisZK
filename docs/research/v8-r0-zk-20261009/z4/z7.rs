//! Z7 (LOG D20): alpha-structure probe. Exact M31/QM31 arithmetic only.
//!
//! Every rank/elimination routine is Z4c's, called unchanged from the parent
//! module (`Ech`, `lane_eliminate`, `compensated_rows`, `pure_c`, `full_c`,
//! `copied_ech`, `initial_zero`, `summarize`, `raw_c`, `tail_row`, `round_row`,
//! `compute_targets`, `normalized`, `normalize_d`, `final_value`). The challenge
//! and tape replay below is z6.rs's `trial` (itself z4c_main's RNG order) with
//! `z` and the query set also returned. `pure_h` is `pure_c`'s body copied
//! verbatim except for one row filter on the mask-only lanes (structure H).
//! `round_polys` is `last_coeff`'s chain reconstruction, returning every round.
use super::*;

const MASTER: u64 = 0x5348f0b9a87835d0;
const STRUCT_SEED: u64 = 0x5a37_d20a_2026_1013;
const STRUCTURES: [&str; 8] = ["A", "B", "C", "D", "E", "F", "G", "H"];

struct Trial {
    a: [QM31; 10],
    z: [Point<QM31>; 2],
    qs: Vec<usize>,
    ch: Challenges,
    tapes: Vec<Trace>,
}
/// Exact replay of z4c_main's RNG consumption (challenges, then five tapes).
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
fn f_rank(xs: &[QM31]) -> usize {
    let mut e = Ech::new(4);
    for x in xs {
        e.insert(limbs(*x).to_vec());
    }
    e.rank
}
fn half() -> QM31 {
    QM31::from_m31(M31(2).inv())
}
fn admissible(a: &[QM31; 10]) -> bool {
    a.iter().all(|x| *x != QM31::ZERO && *x != QM31::ONE) && a[9] != half()
}
fn f_elem(rng: &mut Rng) -> QM31 {
    QM31::from_m31(rng.m())
}
/// Random element of F \ {0,1} (and != 1/2 when `last`).
fn f_nontrivial(rng: &mut Rng, last: bool) -> QM31 {
    loop {
        let x = f_elem(rng);
        if x != QM31::ZERO && x != QM31::ONE && !(last && x == half()) {
            return x;
        }
    }
}
/// Random element of W = span_F{1,x,y} outside {0,1}.
fn w_elem(rng: &mut Rng, w: &[QM31; 3]) -> QM31 {
    loop {
        let v = w[0].mul(f_elem(rng)).add(w[1].mul(f_elem(rng))).add(w[2].mul(f_elem(rng)));
        if v != QM31::ZERO && v != QM31::ONE {
            return v;
        }
    }
}
/// Alpha for a structure. Z4c's uniform coordinates are kept wherever the
/// structure leaves a coordinate uniform in K; structured ones come from a
/// separate per-(structure,vector) stream, so the Z4c stream is untouched.
fn alpha_for(s: &str, v: usize, base: &[QM31; 10]) -> ([QM31; 10], Option<[QM31; 3]>) {
    let si = STRUCTURES.iter().position(|x| *x == s).unwrap() as u64;
    let mut rng = Rng(STRUCT_SEED.wrapping_add((si * 64 + v as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15)));
    let mut a = *base;
    let mut w = None;
    match s {
        "A" | "H" => {}
        "B" => {
            for i in 0..10 {
                a[i] = f_nontrivial(&mut rng, i == 9);
            }
        }
        "C" | "D" | "E" => {
            let basis = loop {
                let b = [QM31::ONE, rng.q(), rng.q()];
                if f_rank(&b) == 3 {
                    break b;
                }
            };
            let k = match s { "C" => 5, "D" => 6, _ => 7 };
            for i in 0..k {
                a[i] = w_elem(&mut rng, &basis);
            }
            w = Some(basis);
        }
        "F" => loop {
            let x = QM31::ONE.mul(f_elem(&mut rng)).add(a[0].mul(f_elem(&mut rng)));
            if x != QM31::ZERO && x != QM31::ONE {
                a[1] = x;
                break;
            }
        },
        "G" => {
            for i in 5..10 {
                a[i] = f_nontrivial(&mut rng, i == 9);
            }
        }
        _ => panic!("unknown structure {s}"),
    }
    assert!(admissible(&a), "alpha admissibility");
    (a, w)
}

/// `last_coeff`'s chain reconstruction, returning all ten 28-coefficient polys.
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
/// Per-round F-ranks: full 28-coefficient projection (max 112) and per tower
/// limb k (max 28), from a list of spanning vectors.
struct Proj {
    full: Vec<Ech<M31>>,
    limb: Vec<Vec<Ech<M31>>>,
}
impl Proj {
    fn new() -> Self {
        Proj {
            full: (0..10).map(|_| Ech::new(112)).collect(),
            limb: (0..10).map(|_| (0..4).map(|_| Ech::new(28)).collect()).collect(),
        }
    }
    fn add_poly(&mut self, j: usize, co: &[QM31; 28]) {
        self.full[j].insert(flatten(co));
        for k in 0..4 {
            self.limb[j][k].insert(co.iter().map(|x| limbs(*x)[k]).collect());
        }
    }
    fn add(&mut self, v: &[QM31], a: &[QM31; 10]) {
        for (j, co) in round_polys(v, a).iter().enumerate() {
            self.add_poly(j, co);
        }
    }
    fn of_ech(e: &Ech<M31>, a: &[QM31; 10]) -> Self {
        let mut p = Proj::new();
        for b in e.p.iter().flatten() {
            p.add(&unflat(b), a);
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
/// Leading-degree pivots of an F-subspace of K[X]_{<=27}: coordinates ordered
/// (degree descending, limb ascending); returns per degree the number of
/// pivots (F-dimension of leading coefficients at that degree).
fn leading(polys: &[[QM31; 28]]) -> [usize; 28] {
    let mut e = Ech::new(112);
    let mut counts = [0usize; 28];
    for co in polys {
        let v: Vec<M31> = (0..28).rev().flat_map(|d| limbs(co[d])).collect();
        if let Some(i) = e.insert(v) {
            counts[27 - i / 4] += 1;
        }
    }
    counts
}
fn degree_set(c: &[usize; 28]) -> String {
    let d: Vec<usize> = (0..28).filter(|&d| c[d] > 0).collect();
    format!("{d:?}")
}

/// Lane generators of the unconstrained image: F-span for mask-only lanes
/// 0..9, K-span for G (c=10) and for D's own word (tail rows).
fn lane_generators(a: &[QM31; 10], tail: &[Vec<QM31>], lane: usize, rows: &[usize]) -> Vec<Vec<QM31>> {
    let mut out = vec![];
    for &r in rows {
        if lane < 10 {
            out.push(round_row(a, r, lane));
        } else {
            let v = if lane == 10 { round_row(a, r, 10) } else { tail[r].clone() };
            for k in 0..4 {
                out.push(v.iter().map(|x| x.mul(tower(k))).collect());
            }
        }
    }
    out
}

/// `pure_c` (libra=true) with mask-only lanes restricted to `keep` rows.
/// Copied from pure_c verbatim; the only change is the row filter on br/rr.
fn pure_h(
    a: &[QM31; 10],
    br: &[Vec<M31>],
    gr: &[Vec<QM31>],
    tail: &[Vec<QM31>],
    keep: &dyn Fn(usize) -> bool,
) -> Ech<M31> {
    let libra = true;
    let mut image = Ech::new(1084);
    let cols: Vec<_> = (0..11).collect();
    for (position, c) in cols.into_iter().enumerate() {
        let lane = if c == 10 { 27 } else { 16 + position };
        let rr = compensated_rows(a, Some(c), lane, tail, libra);
        if c == 10 {
            lane_eliminate(gr, &rr, &[], true, &mut image);
        } else {
            let rows: Vec<usize> = (0..N).filter(|&r| keep(r)).collect();
            let brs: Vec<Vec<M31>> = rows.iter().map(|&r| br[r].clone()).collect();
            let rrs: Vec<Vec<QM31>> = rows.iter().map(|&r| rr[r].clone()).collect();
            lane_eliminate(&brs, &rrs, &[], false, &mut image);
        }
    }
    image
}

fn tail_sum_counts() -> Vec<usize> {
    (0..10)
        .map(|j| {
            let w: Vec<u64> = (j + 1..10).map(|i| 3 + 22 * i as u64).collect();
            let mut s = std::collections::BTreeSet::new();
            for m in 0..1u64 << w.len() {
                s.insert((0..w.len()).filter(|&b| m >> b & 1 == 1).map(|b| w[b]).sum::<u64>());
            }
            s.len()
        })
        .collect()
}
fn lambda_dims(a: &[QM31; 10]) -> (Vec<usize>, Vec<usize>) {
    // Lambda_j = span_F{eqPrefix(alpha, l) : l in {0,1}^j}; S_j = span_F{1, alpha_0..alpha_{j-1}}.
    let mut lam = vec![];
    let mut spans = vec![];
    for j in 0..10 {
        let mut e = Ech::new(4);
        for l in 0..1usize << j {
            let x = (0..j).fold(QM31::ONE, |v, i| {
                v.mul(if l >> i & 1 == 1 { a[i] } else { QM31::ONE.sub(a[i]) })
            });
            e.insert(limbs(x).to_vec());
        }
        lam.push(e.rank);
        let mut s = vec![QM31::ONE];
        s.extend_from_slice(&a[..j]);
        spans.push(f_rank(&s));
    }
    (lam, spans)
}

fn report(label: &str, kind: &str, total: usize, p: &Proj) {
    println!(
        "Z7_RANKS {label} kind={kind} total={total} round_full={:?} round_limb={:?}",
        p.full_ranks(),
        p.limb_ranks()
    );
}

pub(super) fn main() {
    let args: Vec<_> = std::env::args().collect();
    let get = |k: &str| args.windows(2).find(|x| x[0] == k).map(|x| x[1].clone());
    let s = get("--structure").expect("--structure");
    let v: usize = get("--vector").expect("--vector").parse().unwrap();
    let preflight = args.iter().any(|x| x == "--preflight");
    let start = Instant::now();
    println!("Z7_START structure={s} vector={v} preflight={preflight} transport=D13 libra=true gamma=7");
    println!("Z7_TAILSUMS w=3+22i counts={:?}", tail_sum_counts());
    let t = trial(v);
    let (a, w) = alpha_for(&s, v, &t.a);
    let label = format!("structure={s} vector={v}");
    let (lam, spans) = lambda_dims(&a);
    println!(
        "Z7_ALPHA {label} alpha={:?} w_basis={:?} f_coordinates={:?} lambda_dims={lam:?} span_dims={spans:?} alpha9_half={}",
        a.map(l4),
        w.map(|b| b.map(l4)),
        (0..10).filter(|&i| limbs(a[i])[1..] == [M31::ZERO; 3]).collect::<Vec<_>>(),
        a[9] == half()
    );
    let (br, gr) = raw_c(&a, &t.z, &t.qs);
    let tail: Vec<_> = (0..N).map(|r| tail_row(&a, r)).collect();

    if s == "H" {
        // Round-j matrix: mask-only words restricted to rows whose prefix
        // coordinates r_0..r_{j-1} (round_row bit 9-i) are all zero.
        let mut silent_j = vec![];
        let mut unc_j = vec![];
        let mut silent_limb = vec![];
        let mut unc_limb = vec![];
        let mut totals = vec![];
        for j in 0..10 {
            let keep = move |r: usize| (r >> (10 - j)) == 0;
            let pure = pure_h(&a, &br, &gr, &tail, &keep);
            let silent = initial_zero(copied_ech(&pure));
            let ps = Proj::of_ech(&silent, &a);
            silent_j.push(ps.full_ranks()[j]);
            silent_limb.push(ps.limb_ranks()[j]);
            totals.push((silent.rank, pure.rank));
            let mut pu = Proj::new();
            let rows: Vec<usize> = (0..N).filter(|&r| keep(r)).collect();
            let all: Vec<usize> = (0..N).collect();
            for lane in 0..12 {
                let rs = if lane < 10 { &rows } else { &all };
                for g in lane_generators(&a, &tail, lane, rs) {
                    pu.add_poly(j, &round_polys(&g, &a)[j]);
                }
            }
            unc_j.push(pu.full_ranks()[j]);
            unc_limb.push(pu.limb_ranks()[j]);
            println!("Z7_H_PROGRESS {label} round={j} rows_per_mask_lane={} silent_total={} initial_retained_total={}", rows.len(), silent.rank, pure.rank);
        }
        println!("Z7_RANKS {label} kind=silent_H total_per_round_matrix={:?} round_full={silent_j:?} round_limb={silent_limb:?}", totals.iter().map(|x| x.0).collect::<Vec<_>>());
        println!("Z7_RANKS {label} kind=unconstrained_H round_full={unc_j:?} round_limb={unc_limb:?}");
        println!("Z7_TARGETS {label} computed=false reason=H_round_matrices_are_not_one_image_ranks_only");
        println!("Z7_DONE {label} wall_seconds={:.3}", start.elapsed().as_secs_f64());
        return;
    }

    let pure = pure_c(&a, &br, &gr, &tail, true);
    let silent = initial_zero(copied_ech(&pure));
    report(&label, "silent", silent.rank, &Proj::of_ech(&silent, &a));
    report(&label, "silent_initial_retained", pure.rank, &Proj::of_ech(&pure, &a));
    // Unconstrained pure image: every lane word free (mask-only F, G and D K).
    let all: Vec<usize> = (0..N).collect();
    let mut unc = Ech::new(1084);
    let mut unc_p = Proj::new();
    let mut lane_unc: Vec<Vec<Vec<[QM31; 28]>>> = vec![vec![vec![]; 10]; 12];
    for lane in 0..12 {
        for g in lane_generators(&a, &tail, lane, &all) {
            let polys = round_polys(&g, &a);
            for j in 0..10 {
                unc_p.add_poly(j, &polys[j]);
                if s == "A" && (5..8).contains(&j) {
                    lane_unc[lane][j].push(polys[j]);
                }
            }
            if unc.rank < 1084 {
                unc.insert(flatten(&g));
            }
        }
    }
    report(&label, "unconstrained", unc.rank, &unc_p);
    if s == "A" {
        assert_eq!(silent.rank, 1076, "stop rule: structure A silent rank");
        // Per-lane leading-degree pivots at rounds 5-7. Silent: each lane's own
        // lane_eliminate image (with its D compensation, initial retained).
        for lane in 0..12 {
            let name = match lane { 10 => "G".to_string(), 11 => "D".to_string(), c => format!("mask{c}_e{}", EXP[c]) };
            let mut own = Ech::new(1084);
            if lane < 11 {
                let lid = if lane == 10 { 27 } else { 16 + lane };
                let rr = compensated_rows(&a, Some(lane), lid, &tail, true);
                if lane == 10 {
                    lane_eliminate(&gr, &rr, &[], true, &mut own);
                } else {
                    lane_eliminate(&br, &rr, &[], false, &mut own);
                }
            }
            let own_polys: Vec<Vec<[QM31; 28]>> = {
                let mut x = vec![vec![]; 10];
                for b in own.p.iter().flatten() {
                    let ps = round_polys(&unflat(b), &a);
                    for j in 5..8 {
                        x[j].push(ps[j]);
                    }
                }
                x
            };
            for j in 5..8 {
                let cu = leading(&lane_unc[lane][j]);
                println!("Z7_PIVOTS {label} lane={name} round={j} kind=unconstrained degrees={} per_degree_dims={cu:?}", degree_set(&cu));
                if lane < 11 {
                    let cs = leading(&own_polys[j]);
                    println!("Z7_PIVOTS {label} lane={name} round={j} kind=silent_lane_own degrees={} per_degree_dims={cs:?} lane_rank={}", degree_set(&cs), own.rank);
                }
            }
        }
    }
    if preflight {
        println!("Z7_PREFLIGHT_DONE {label} wall_seconds={:.3}", start.elapsed().as_secs_f64());
        return;
    }
    // Chain0 basis: initial 0 and terminal value 0 (stored coordinates);
    // normalized units span the 1,076-dimensional upper-bound space.
    let chain0: Vec<Vec<M31>> = (4..1084)
        .map(|i| {
            let mut u = vec![M31::ZERO; 1084];
            u[i] = M31::ONE;
            let q = unflat(&u);
            let phi = final_value(&q, &a);
            flatten(&normalize_d(&q, phi, &a).expect("alpha9=1/2"))
        })
        .collect();
    summarize(&format!("{label} chain0_basis"), &silent, &chain0);
    // Z4c's honest targets (i', derivative diagnostic, ii') at this alpha.
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
            "Z7_TERMINAL {label} pair={pair} pinned={:?} derivative={:?} ii={:?}",
            l4(original.terminal[0]),
            l4(original.terminal[1]),
            l4(original.terminal[2])
        );
        targets.push(normalized(&original, &a, &traces[2 * pair], &traces[2 * pair + 1], &ch, public));
    }
    let i: Vec<_> = targets.iter().map(|t| flatten(&t.pinned)).collect();
    let derivative: Vec<_> = targets.iter().map(|t| flatten(&t.derivative)).collect();
    let (full, ii) = full_c(&a, &br, &gr, &tail, &traces, &targets, &pure, true);
    summarize(&format!("{label} libra_i_prime"), &silent, &i);
    summarize(&format!("{label} libra_derivative_diagnostic"), &silent, &derivative);
    summarize(&format!("{label} libra_ii_prime"), &full, &ii);
    println!(
        "Z7_GATE {label} silent_rank={} initial_retained_rank={} full_conditioned_rank={} i_pass={} ii_pass={} attempted=5",
        silent.rank,
        pure.rank,
        full.rank,
        pass_count(&silent, &i),
        pass_count(&full, &ii)
    );
    println!("Z7_DONE {label} wall_seconds={:.3}", start.elapsed().as_secs_f64());
}
