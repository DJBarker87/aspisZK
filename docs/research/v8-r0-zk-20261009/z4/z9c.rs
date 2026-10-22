//! Z9c (LOG D38.5; zf1/DESIGN-P-CERT.txt): certificate emission and checking for
//! the R1 prover-side predicate P_R1, on the real R1 payload of Z9/Z9b.
//!
//! * `emit` is the producer (tagged eliminations; any code, never proved).
//! * `check` is the checker: it recomputes the source columns from the
//!   challenges and verifies the certificate with dot products and equality
//!   tests over M31 only (no elimination, no division).
//!
//! A child module of z9b (reuses its relation builders and query sets).
//! Exact arithmetic. Not a Lean proof.
use super::*;
use std::time::Instant;

// ------------------------------------------------------------ M31 kernel
const PU: u32 = 0x7fff_ffff;
const PM: u64 = 0x7fff_ffff;
#[inline(always)]
fn red(x: u64) -> u32 {
    let x = (x & PM) + (x >> 31);
    let x = (x & PM) + (x >> 31);
    let x = x as u32;
    if x >= PU { x - PU } else { x }
}
#[inline(always)]
fn mulm(a: u32, b: u32) -> u32 {
    red(a as u64 * b as u64)
}
#[inline(always)]
fn addm(a: u32, b: u32) -> u32 {
    let s = a + b;
    if s >= PU { s - PU } else { s }
}
#[inline(always)]
fn subm(a: u32, b: u32) -> u32 {
    if a >= b { a - b } else { a + PU - b }
}
#[inline(always)]
fn negm(a: u32) -> u32 {
    if a == 0 { 0 } else { PU - a }
}
fn invm(a: u32) -> u32 {
    M31(a).inv().0
}
/// Lazy-accumulated dot product: each term folded to < 2^32, one reduction.
#[inline]
fn dot(a: &[u32], b: &[u32]) -> u32 {
    debug_assert_eq!(a.len(), b.len());
    let mut s = [0u64; 4];
    let n4 = a.len() / 4 * 4;
    let (a4, ar) = a.split_at(n4);
    let (b4, br) = b.split_at(n4);
    for (x, y) in a4.chunks_exact(4).zip(b4.chunks_exact(4)) {
        for k in 0..4 {
            let p = x[k] as u64 * y[k] as u64;
            s[k] += (p & PM) + (p >> 31);
        }
    }
    let mut t = s[0] % PM + s[1] % PM + s[2] % PM + s[3] % PM;
    for (x, y) in ar.iter().zip(br) {
        let p = *x as u64 * *y as u64;
        t += (p & PM) + (p >> 31);
    }
    red(t)
}
/// v -= s * b  (elementwise, from index `from`).
#[inline]
fn axpy_sub(v: &mut [u32], s: u32, b: &[u32]) {
    let n = core::cmp::min(v.len(), b.len());
    let tiled = n / 8 * 8;
    for (x,y) in v[..tiled].chunks_exact_mut(8).zip(b[..tiled].chunks_exact(8)) {
        for k in 0..8 { x[k] = aspis_r1_cert_check::native_m31::sub_product(x[k],s,y[k]); }
    }
    for (x,y) in v[tiled..n].iter_mut().zip(&b[tiled..n]) {
        *x = aspis_r1_cert_check::native_m31::sub_product(*x,s,*y);
    }
}
fn scale_in(v: &mut [u32], s: u32) {
    for x in v.iter_mut() {
        *x = mulm(*x, s);
    }
}
fn u(v: &[M31]) -> Vec<u32> {
    v.iter().map(|x| x.0).collect()
}
/// Row-major transpose of `cols` (each of length `h`) into `h` rows of length cols.len().
fn transpose(cols: &[&[u32]], h: usize) -> Vec<Vec<u32>> {
    (0..h).map(|t| cols.iter().map(|c| c[t]).collect()).collect()
}

// ------------------------------------------------------------ tagged elimination
/// Streaming elimination that records, for each pivot row, its combination of
/// the inserted vectors (tags over pivot positions, in insertion order of pivots).
struct TagEch {
    piv: Vec<Option<usize>>, // column -> row
    rows: Vec<(Vec<u32>, Vec<u32>)>,
    cols: Vec<usize>, // row -> pivot column
}
enum Ins {
    Pivot,
    /// The vector reduced to zero: v + sum_p t_p (pivot vector p) = 0.
    Zero(Vec<u32>),
}
impl TagEch {
    fn new(width: usize) -> Self {
        TagEch { piv: vec![None; width], rows: vec![], cols: vec![] }
    }
    fn rank(&self) -> usize {
        self.rows.len()
    }
    /// Insert v (tag = unit on itself). Pivot rows keep tags over pivot indices;
    /// a new pivot takes the next pivot index.
    fn insert(&mut self, mut v: Vec<u32>) -> Ins {
        let mut t = vec![0u32; self.rows.len() + 1];
        let me = self.rows.len();
        t[me] = 1;
        for i in 0..v.len() {
            if v[i] == 0 {
                continue;
            }
            if let Some(k) = self.piv[i] {
                let s = v[i];
                let (b, bt) = &self.rows[k];
                axpy_sub(&mut v[i..], s, &b[i..]);
                axpy_sub(&mut t[..bt.len()], s, bt);
            } else {
                let inv = invm(v[i]);
                scale_in(&mut v[i..], inv);
                scale_in(&mut t, inv);
                self.piv[i] = Some(me);
                self.rows.push((v, t));
                self.cols.push(i);
                return Ins::Pivot;
            }
        }
        // v reduced to 0: t[me] = 1 and 0 = v + sum_{p<me} t_p row-sources.
        t.truncate(me);
        Ins::Zero(t)
    }
    /// Reduce v; Some(y) with v = sum_k y_k (inserted pivot vector k) if v is in the span.
    fn express(&self, mut v: Vec<u32>) -> Option<Vec<u32>> {
        let mut y = vec![0u32; self.rows.len()];
        for i in 0..v.len() {
            if v[i] == 0 {
                continue;
            }
            let k = self.piv[i]?;
            let s = v[i];
            let (b, bt) = &self.rows[k];
            axpy_sub(&mut v[i..], s, &b[i..]);
            // v_old = s * row_k + v_new, row_k = sum bt_e src_e
            for (e, x) in bt.iter().enumerate() {
                y[e] = addm(y[e], mulm(s, *x));
            }
        }
        Some(y)
    }
}
/// Pivot tags are combinations of inserted *pivot* vectors: row_k.v = sum_e tag_e * src_e
/// where src_e is the e-th vector that became a pivot.  `Zero(t)` means
/// src_new + sum_e t_e src_e = 0 (t over pivot sources).
fn kernel_coeffs(t: Vec<u32>) -> Vec<u32> {
    t
}

// ------------------------------------------------------------ source data
/// Public data the checker and producer both recompute from the challenges.
struct Pub {
    a: [QM31; 10],
    qs: Vec<usize>,
    lay: Lay,
    cx: Ctx,
    rels: Vec<Vec<u32>>, // relR1 limb functionals on the 1328 read-support coordinates
    z: [Point<QM31>; 2], // the OOD points (for the C3 lift-builder differential)
    op: Opening,         // the openings (for the C3 relation-builder differential)
}
const BAT0: usize = 8; // the probe's inactive cell (not an R1Bat cell) occupies limbs 0..8
struct Src3 {
    own: Vec<u32>,
    round: Vec<u32>,
    bat: Vec<u32>,
}
fn build_pub(s: &str, v: usize, qspec: &str, gi: usize) -> Pub {
    let pi = d18_transport();
    // The transport is a process-wide OnceLock; the checker's rebuild reuses it.
    if z5::is_selected() {
        assert_eq!(*z5::transport(), pi, "D18 transport");
    } else {
        z5::set_transport(pi);
    }
    let t = trial(v);
    let a = alpha_for(s, v, &t.a);
    let qs = query_set(qspec, &t.qs);
    let op = opening_challenges(v, gi);
    let lay = Lay::new(&qs);
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
    let wd = weights_design(&a, &t.z, op.kappa);
    let dr = design_relations(&wd, &op, &qs, &lay);
    let mut rl: Vec<&Rel> = vec![&dr.s2a, &dr.s2b, &dr.s1];
    rl.extend(dr.circ.iter());
    rl.extend(dr.line[1].iter());
    let rels = rl.iter().flat_map(|r| r.limb_functionals(lay.bw)).map(|f| u(&f[BAT0..])).collect();
    Pub { a, qs, lay, cx, rels, z: t.z, op }
}
fn src3(ln: &Lanes, li: usize, i: usize) -> Src3 {
    let (o, b, r) = ln.bal(li, i);
    Src3 { own: u(&o), round: u(&flatten(&r)), bat: u(&wflat(&b)[BAT0..]) }
}
/// ChainT0K4 generators b_i = normalize_d(e_i) in the Z4c round coordinates.
fn chain_targets(a: &[QM31; 10]) -> Vec<Vec<u32>> {
    (0..RW)
        .map(|i| {
            let mut e = vec![M31::ZERO; RW];
            e[i] = M31::ONE;
            let q = unflat(&e);
            let ph = final_value(&q, a);
            u(&flatten(&normalize_d(&q, ph, a).expect("HalfOK")))
        })
        .collect()
}
/// Lift sources: (C1 lane c < 16) eligible rows r != 1023 balanced at 1023, F lane obs;
/// (c = 16, H1) inactive rows r >= 1, 4 tower limbs, balanced at 0, K4 obs.
fn lift_src(cx: &Ctx, c: usize, idx: u32) -> Vec<u32> {
    if c < 16 {
        let r = idx as usize;
        if inactive(r) { u(&sub_vec(&cx.br[r][1..], &cx.br[1023][1..], |x, y| x.sub(y))) } else { u(&cx.br[r][1..]) }
    } else {
        let (r, k) = (idx as usize / 4, idx as usize % 4);
        let g = if inactive(r) { sub_vec(&cx.gr[r][1..], &cx.gr[0][1..], |p, q| p.sub(q)) } else { cx.gr[r][1..].to_vec() };
        u(&flatten(&scale(&g, tower(k))))
    }
}
fn lift_members(c: usize) -> Vec<u32> {
    if c < 16 {
        (0..N).filter(|&r| r != 1023 && eligible(c, r)).map(|r| r as u32).collect()
    } else {
        (1..N).filter(|&r| inactive(r)).flat_map(|r| (0..4).map(move |k| (4 * r + k) as u32)).collect()
    }
}
fn lift_width(c: usize) -> usize {
    if c < 16 { 112 } else { DW }
}

// ------------------------------------------------------------ certificate
#[derive(Clone)]
struct LaneKer {
    lane: u32,
    piv: Vec<u32>,              // source indices of the lane
    ents: Vec<(u32, Vec<u32>)>, // (source j, c over piv): k = s_j + sum_p c_p s_p
}
#[derive(Clone)]
struct Lift {
    sel: Vec<u32>,     // member indices (row for C1, 4r+k for H1)
    uinv: Vec<Vec<u32>>, // w x w, O_S * uinv = I
}
#[derive(Clone)]
struct Cert {
    hinv: [u32; 4],
    qp: Vec<LaneKer>,
    qp_y: Vec<Vec<u32>>, // RW rows over all entries (lane order)
    bc_u: Vec<Vec<u32>>, // r x q
    bc_piv: Vec<u32>,
    bc_fr: Vec<u32>,
    bc_g: LaneKer,
    bc_y: Vec<Vec<u32>>, // |fr| rows over bc_g entries
    lifts: Vec<Lift>,    // 16 C1 then H1
}
impl Cert {
    fn limbs(&self) -> usize {
        let lk = |l: &LaneKer| 1 + l.piv.len() + l.ents.iter().map(|(_, c)| 1 + c.len()).sum::<usize>();
        let mat = |m: &Vec<Vec<u32>>| m.iter().map(|r| r.len()).sum::<usize>();
        4 + self.qp.iter().map(lk).sum::<usize>()
            + mat(&self.qp_y)
            + mat(&self.bc_u)
            + self.bc_piv.len()
            + self.bc_fr.len()
            + lk(&self.bc_g)
            + mat(&self.bc_y)
            + self.lifts.iter().map(|l| l.sel.len() + mat(&l.uinv)).sum::<usize>()
    }
}
fn ql(x: QM31) -> [u32; 4] {
    limbs(x).map(|v| v.0)
}

/// Gauss-Jordan inverse of a square matrix (producer side).
fn invert(m: &[Vec<u32>]) -> Option<Vec<Vec<u32>>> {
    let n = m.len();
    let mut a: Vec<Vec<u32>> = m
        .iter()
        .enumerate()
        .map(|(i, r)| {
            let mut x = r.clone();
            x.extend((0..n).map(|j| (i == j) as u32));
            x
        })
        .collect();
    for c in 0..n {
        let p = (c..n).find(|&i| a[i][c] != 0)?;
        a.swap(c, p);
        let inv = invm(a[c][c]);
        scale_in(&mut a[c], inv);
        let pr = a[c].clone();
        for i in 0..n {
            if i != c && a[i][c] != 0 {
                let s = a[i][c];
                axpy_sub(&mut a[i], s, &pr);
            }
        }
    }
    Some(a.into_iter().map(|r| r[n..].to_vec()).collect())
}

// ------------------------------------------------------------ producer
#[derive(Default, Debug)]
struct EmitInfo {
    rank_r: usize,
    qp_entries: usize,
    qp_lanes_used: usize,
    rel_rank: usize,
    vg_rank: usize,
    g_piv: usize,
    lift_ranks: Vec<usize>,
    fail: Option<&'static str>,
    t_lifts: f64,
    t_qprime: f64,
    t_bcond: f64,
}
fn emit(p: &Pub) -> (Option<Cert>, EmitInfo) {
    let mut info = EmitInfo::default();
    let a = &p.a;
    let half = QM31::from_m31(M31(2).inv());
    let hinv = match a[9].sub(half).try_inv() {
        Some(x) => ql(x),
        None => {
            info.fail = Some("HalfOK");
            return (None, info);
        }
    };
    let ln = Lanes::new(&p.cx);
    // Lifts.
    let mut tt = Instant::now();
    let mut lifts = vec![];
    for c in 0..17 {
        let w = lift_width(c);
        let mut e = TagEch::new(w);
        let mut sel = vec![];
        for m in lift_members(c) {
            if let Ins::Pivot = e.insert(lift_src(&p.cx, c, m)) {
                sel.push(m);
                if sel.len() == w {
                    break;
                }
            }
        }
        info.lift_ranks.push(sel.len());
        if sel.len() < w {
            info.fail = Some("lift rank below width");
            return (None, info);
        }
        // O_S: column t = obs(src sel[t]); O_S * U = I  <=>  U = O_S^-1.
        let cols: Vec<Vec<u32>> = sel.iter().map(|&m| lift_src(&p.cx, c, m)).collect();
        let os = transpose(&cols.iter().map(|c| c.as_slice()).collect::<Vec<_>>(), w);
        let uinv = invert(&os).expect("selected columns are independent");
        lifts.push(Lift { sel, uinv });
    }
    info.t_lifts = tt.elapsed().as_secs_f64();
    tt = Instant::now();
    // QPrime: per-lane own kernel vectors, round images into a tagged echelon R.
    let targets = chain_targets(a);
    let mut rech = TagEch::new(RW);
    let mut kept: Vec<LaneKer> = vec![];
    let mut qp_y: Option<Vec<Vec<u32>>> = None;
    let try_targets = |rech: &TagEch| -> Option<Vec<Vec<u32>>> { targets.iter().map(|b| rech.express(b.clone())).collect() };
    'lanes: for li in 0..LANES {
        let mut own = TagEch::new(own_width(li));
        let mut piv: Vec<u32> = vec![];
        let mut piv_round: Vec<Vec<u32>> = vec![];
        let mut lk = LaneKer { lane: li as u32, piv: vec![], ents: vec![] };
        for i in 0..ln.count(li) {
            let s = src3(&ln, li, i);
            match own.insert(s.own.clone()) {
                Ins::Pivot => {
                    piv.push(i as u32);
                    piv_round.push(s.round);
                }
                Ins::Zero(t) => {
                    let c = kernel_coeffs(t);
                    let mut rho = s.round.clone();
                    for (pidx, cp) in c.iter().enumerate() {
                        if *cp != 0 {
                            // rho = round_j + sum c_p round_p
                            axpy_sub(&mut rho, negm(*cp), &piv_round[pidx]);
                        }
                    }
                    if let Ins::Pivot = rech.insert(rho) {
                        lk.ents.push((i as u32, c));
                        if rech.rank() >= 1080 {
                            if let Some(y) = try_targets(&rech) {
                                lk.piv = piv.clone();
                                kept.push(lk.clone());
                                qp_y = Some(y);
                                break 'lanes;
                            }
                        }
                    }
                }
            }
        }
        lk.piv = piv;
        if !lk.ents.is_empty() {
            kept.push(lk);
        }
    }
    info.rank_r = rech.rank();
    if qp_y.is_none() {
        qp_y = try_targets(&rech);
    }
    let Some(qp_y) = qp_y else {
        info.fail = Some("QPrime_R1");
        info.t_qprime = tt.elapsed().as_secs_f64();
        return (None, info);
    };
    // Entry e of R (in pivot order) is the e-th kept entry in lane order (pivot order = push order).
    info.qp_entries = kept.iter().map(|l| l.ents.len()).sum();
    info.qp_lanes_used = kept.len();
    info.t_qprime = tt.elapsed().as_secs_f64();
    tt = Instant::now();
    // BCondG: reduced echelon of Rel with tags.
    let bwr = p.lay.bw - BAT0;
    let q = p.rels.len();
    let mut re = TagEch::new(bwr);
    let mut relpiv_src: Vec<usize> = vec![]; // which relation row each pivot came from
    for (k, f) in p.rels.iter().enumerate() {
        if let Ins::Pivot = re.insert(f.clone()) {
            relpiv_src.push(k);
        }
    }
    let r = re.rank();
    info.rel_rank = r;
    // Back-substitute to reduced form; tags are over pivot-source relations -> map to all q.
    let mut rows: Vec<(Vec<u32>, Vec<u32>)> = re
        .rows
        .iter()
        .map(|(v, t)| {
            let mut uq = vec![0u32; q];
            for (e, x) in t.iter().enumerate() {
                uq[relpiv_src[e]] = *x;
            }
            (v.clone(), uq)
        })
        .collect();
    let cols = re.cols.clone();
    for k in 0..r {
        let ck = cols[k];
        let (pv, pt) = rows[k].clone();
        for k2 in 0..r {
            if k2 != k && rows[k2].0[ck] != 0 {
                let s = rows[k2].0[ck];
                axpy_sub(&mut rows[k2].0, s, &pv);
                axpy_sub(&mut rows[k2].1, s, &pt);
            }
        }
    }
    let bc_piv: Vec<u32> = cols.iter().map(|&c| c as u32).collect();
    let bc_fr: Vec<u32> = (0..bwr).filter(|c| re.piv[*c].is_none()).map(|c| c as u32).collect();
    let nvec: Vec<Vec<u32>> = bc_fr
        .iter()
        .map(|&f| {
            let mut n = vec![0u32; bwr];
            n[f as usize] = 1;
            for k in 0..r {
                n[cols[k]] = negm(rows[k].0[f as usize]);
            }
            n
        })
        .collect();
    let bc_u: Vec<Vec<u32>> = rows.iter().map(|(_, t)| t.clone()).collect();
    // V_G: G lane kernel of [own; round], bat images into a tagged echelon.
    let g = 10;
    let mut zero = TagEch::new(own_width(g) + RW);
    let mut gpiv: Vec<u32> = vec![];
    let mut gpiv_bat: Vec<Vec<u32>> = vec![];
    let mut gk = LaneKer { lane: g as u32, piv: vec![], ents: vec![] };
    let mut vech = TagEch::new(bwr);
    let mut bc_y = None;
    let try_n = |vech: &TagEch| -> Option<Vec<Vec<u32>>> { nvec.iter().map(|n| vech.express(n.clone())).collect() };
    for i in 0..ln.count(g) {
        let s = src3(&ln, g, i);
        let mut zv = s.own.clone();
        zv.extend(&s.round);
        match zero.insert(zv) {
            Ins::Pivot => {
                gpiv.push(i as u32);
                gpiv_bat.push(s.bat);
            }
            Ins::Zero(c) => {
                let mut b = s.bat.clone();
                for (pidx, cp) in c.iter().enumerate() {
                    if *cp != 0 {
                        axpy_sub(&mut b, negm(*cp), &gpiv_bat[pidx]);
                    }
                }
                if let Ins::Pivot = vech.insert(b) {
                    gk.ents.push((i as u32, c));
                    if vech.rank() >= nvec.len() {
                        bc_y = try_n(&vech);
                        if bc_y.is_some() {
                            break;
                        }
                    }
                }
            }
        }
    }
    gk.piv = gpiv;
    info.g_piv = gk.piv.len();
    info.vg_rank = vech.rank();
    if bc_y.is_none() {
        bc_y = try_n(&vech);
    }
    info.t_bcond = tt.elapsed().as_secs_f64();
    let Some(bc_y) = bc_y else {
        info.fail = Some("BCondG_R1");
        return (None, info);
    };
    if p.qs.len() > 22 {
        info.fail = Some("QueryCard");
        return (None, info);
    }
    (Some(Cert { hinv, qp: kept, qp_y, bc_u, bc_piv, bc_fr, bc_g: gk, bc_y, lifts }), info)
}

// ------------------------------------------------------------ checker
#[derive(Default, Debug)]
struct CheckTimes {
    src: f64,
    lifts: f64,
    qprime: f64,
    bcond: f64,
}
/// The checker. Returns (verdict, failing step).
fn check(p: &Pub, c: &Cert, tm: &mut CheckTimes) -> (bool, &'static str) {
    let canon = |v: &[u32]| v.iter().all(|x| *x < PU);
    let canon_m = |m: &[Vec<u32>]| m.iter().all(|r| canon(r));
    // 1. canonical limbs.
    if !canon(&c.hinv) || !canon_m(&c.qp_y) || !canon_m(&c.bc_u) || !canon_m(&c.bc_y) {
        return (false, "canonical");
    }
    for l in c.qp.iter().chain(std::iter::once(&c.bc_g)) {
        if !l.ents.iter().all(|(_, cc)| canon(cc)) {
            return (false, "canonical");
        }
    }
    if !c.lifts.iter().all(|l| canon_m(&l.uinv)) {
        return (false, "canonical");
    }
    // 2. HalfOK, QueryCard, SemK4 (QM31 by type in the probe).
    let half = QM31::from_m31(M31(2).inv());
    let hv = QM31 { c0: CM31::new(M31(c.hinv[0]), M31(c.hinv[1])), c1: CM31::new(M31(c.hinv[2]), M31(c.hinv[3])) };
    if p.a[9].sub(half).mul(hv) != QM31::ONE {
        return (false, "HalfOK");
    }
    if p.qs.len() > 22 {
        return (false, "QueryCard");
    }
    let mut tt = Instant::now();
    let ln = Lanes::new(&p.cx);
    tm.src += tt.elapsed().as_secs_f64();
    // 4. lifts: O_S * U == I.
    tt = Instant::now();
    if c.lifts.len() != 17 {
        return (false, "lift count");
    }
    for (ci, l) in c.lifts.iter().enumerate() {
        let w = lift_width(ci);
        let members = lift_members(ci);
        if l.sel.len() != w || l.uinv.len() != w || l.uinv.iter().any(|r| r.len() != w) || l.sel.iter().any(|m| members.binary_search(m).is_err()) {
            return (false, "lift shape");
        }
        let cols: Vec<Vec<u32>> = l.sel.iter().map(|&m| lift_src(&p.cx, ci, m)).collect();
        let os = transpose(&cols.iter().map(|c| c.as_slice()).collect::<Vec<_>>(), w);
        let ut = transpose(&l.uinv.iter().map(|r| r.as_slice()).collect::<Vec<_>>(), w);
        for i in 0..w {
            for j in 0..w {
                if dot(&os[i], &ut[j]) != (i == j) as u32 {
                    return (false, "lift inverse");
                }
            }
        }
    }
    tm.lifts += tt.elapsed().as_secs_f64();
    // 5. QPrime.
    tt = Instant::now();
    let mut rhos: Vec<Vec<u32>> = vec![];
    for l in &c.qp {
        let li = l.lane as usize;
        if li >= LANES || l.piv.iter().chain(l.ents.iter().map(|(j, _)| j)).any(|&j| j as usize >= ln.count(li)) {
            return (false, "qprime index");
        }
        let ow = own_width(li);
        let ps: Vec<Src3> = l.piv.iter().map(|&j| src3(&ln, li, j as usize)).collect();
        let own_t = transpose(&ps.iter().map(|s| s.own.as_slice()).collect::<Vec<_>>(), ow);
        let rnd_t = transpose(&ps.iter().map(|s| s.round.as_slice()).collect::<Vec<_>>(), RW);
        for (j, cc) in &l.ents {
            // c covers a prefix of the lane's pivot list (the pivots that existed when
            // the entry was produced): KerEntry.s = c.len() <= |P|.
            let n = cc.len();
            if n > l.piv.len() {
                return (false, "qprime shape");
            }
            let s = src3(&ln, li, *j as usize);
            if (0..ow).any(|t| addm(s.own[t], dot(&own_t[t][..n], cc)) != 0) {
                return (false, "qprime kernel");
            }
            rhos.push((0..RW).map(|t| addm(s.round[t], dot(&rnd_t[t][..n], cc))).collect());
        }
    }
    let targets = chain_targets(&p.a);
    if c.qp_y.len() != RW || c.qp_y.iter().any(|r| r.len() != rhos.len()) {
        return (false, "qprime Y shape");
    }
    let rho_t = transpose(&rhos.iter().map(|r| r.as_slice()).collect::<Vec<_>>(), RW);
    for i in 0..RW {
        for t in 0..RW {
            if dot(&c.qp_y[i], &rho_t[t]) != targets[i][t] {
                return (false, "qprime combination");
            }
        }
    }
    tm.qprime += tt.elapsed().as_secs_f64();
    // 6. BCondG.
    tt = Instant::now();
    let bwr = p.lay.bw - BAT0;
    let q = p.rels.len();
    let r = c.bc_piv.len();
    if c.bc_u.len() != r || c.bc_u.iter().any(|x| x.len() != q) || r + c.bc_fr.len() != bwr {
        return (false, "bcond shape");
    }
    // partition: every column in exactly one list.
    let mut seen = vec![0u8; bwr];
    for &x in c.bc_piv.iter().chain(&c.bc_fr) {
        if x as usize >= bwr {
            return (false, "bcond index");
        }
        seen[x as usize] += 1;
    }
    if seen.iter().any(|s| *s != 1) {
        return (false, "bcond partition");
    }
    let rel_t = transpose(&p.rels.iter().map(|x| x.as_slice()).collect::<Vec<_>>(), bwr);
    let e: Vec<Vec<u32>> = c.bc_u.iter().map(|uk| (0..bwr).map(|col| dot(uk, &rel_t[col])).collect()).collect();
    for k in 0..r {
        for k2 in 0..r {
            if e[k][c.bc_piv[k2] as usize] != (k == k2) as u32 {
                return (false, "bcond echelon");
            }
        }
    }
    let g = c.bc_g.lane as usize;
    if g != 10 || c.bc_g.piv.iter().chain(c.bc_g.ents.iter().map(|(j, _)| j)).any(|&j| j as usize >= ln.count(10)) {
        return (false, "bcond G index");
    }
    let zw = own_width(10) + RW;
    let ps: Vec<Src3> = c.bc_g.piv.iter().map(|&j| src3(&ln, 10, j as usize)).collect();
    let zcols: Vec<Vec<u32>> = ps.iter().map(|s| { let mut z = s.own.clone(); z.extend(&s.round); z }).collect();
    let z_t = transpose(&zcols.iter().map(|x| x.as_slice()).collect::<Vec<_>>(), zw);
    let b_t = transpose(&ps.iter().map(|s| s.bat.as_slice()).collect::<Vec<_>>(), bwr);
    let mut betas: Vec<Vec<u32>> = vec![];
    for (j, cc) in &c.bc_g.ents {
        let n = cc.len();
        if n > c.bc_g.piv.len() {
            return (false, "bcond G shape");
        }
        let s = src3(&ln, 10, *j as usize);
        let mut zj = s.own.clone();
        zj.extend(&s.round);
        if (0..zw).any(|t| addm(zj[t], dot(&z_t[t][..n], cc)) != 0) {
            return (false, "bcond G kernel");
        }
        betas.push((0..bwr).map(|t| addm(s.bat[t], dot(&b_t[t][..n], cc))).collect());
    }
    if c.bc_y.len() != c.bc_fr.len() || c.bc_y.iter().any(|y| y.len() != betas.len()) {
        return (false, "bcond Y shape");
    }
    let beta_t = transpose(&betas.iter().map(|x| x.as_slice()).collect::<Vec<_>>(), bwr);
    // n_f = e_{fr f} - sum_k E[k][fr f] e_{piv k}
    let mut is_piv = vec![usize::MAX; bwr];
    for (k, &pc) in c.bc_piv.iter().enumerate() {
        is_piv[pc as usize] = k;
    }
    for (f, &fc) in c.bc_fr.iter().enumerate() {
        for t in 0..bwr {
            let nf = if t == fc as usize { 1 } else if is_piv[t] != usize::MAX { negm(e[is_piv[t]][fc as usize]) } else { 0 };
            if dot(&c.bc_y[f], &beta_t[t]) != nf {
                return (false, "bcond combination");
            }
        }
    }
    tm.bcond += tt.elapsed().as_secs_f64();
    (true, "ok")
}

// ------------------------------------------------------------ teeth
fn bump(x: &mut u32) {
    *x = addm(*x, 1);
}
fn corruptions(c: &Cert) -> Vec<(&'static str, Cert)> {
    let mut out = vec![];
    let mut x = c.clone();
    bump(&mut x.hinv[0]);
    out.push(("hinv", x));
    let mut x = c.clone();
    let l = x.qp.iter_mut().find(|l| l.ents.iter().any(|(_, cc)| !cc.is_empty())).unwrap();
    let e = l.ents.iter_mut().find(|(_, cc)| !cc.is_empty()).unwrap();
    bump(&mut e.1[0]);
    out.push(("qprime kernel coefficient", x));
    let mut x = c.clone();
    bump(&mut x.qp_y[17][5]);
    out.push(("qprime Y entry", x));
    let mut x = c.clone();
    bump(&mut x.bc_u[3][7]);
    out.push(("bcond U entry", x));
    let mut x = c.clone();
    bump(&mut x.bc_y[11][2]);
    out.push(("bcond Y_G entry", x));
    let mut x = c.clone();
    let last = x.bc_g.ents.len() - 1;
    let n = x.bc_g.ents[last].1.len();
    bump(&mut x.bc_g.ents[last].1[n / 2]);
    out.push(("bcond G kernel coefficient", x));
    let mut x = c.clone();
    bump(&mut x.lifts[16].uinv[100][200]);
    out.push(("H1 lift inverse", x));
    let mut x = c.clone();
    let (a, b) = (x.bc_piv[0], x.bc_fr[0]);
    x.bc_piv[0] = b;
    x.bc_fr[0] = a;
    out.push(("swapped pivot/free index", x));
    out
}

pub(crate) fn main() {
    let args: Vec<_> = std::env::args().collect();
    let get = |k: &str| args.windows(2).find(|x| x[0] == k).map(|x| x[1].clone());
    let s = get("--structure").unwrap_or("A".into());
    let v: usize = get("--vector").unwrap_or("0".into()).parse().unwrap();
    let qspec = get("--qset").unwrap_or("actual".into());
    let gi: usize = get("--gamma").unwrap_or("0".into()).parse().unwrap();
    let teeth = args.iter().any(|x| x == "--teeth");
    let label = format!("structure={s} vector={v} qset={qspec} gamma={gi}");
    let t0 = Instant::now();
    let p = build_pub(&s, v, &qspec, gi);
    let t_pub = t0.elapsed().as_secs_f64();
    println!("R1CERT_START {label} queries={} distinct_parents={} bat_width={} relations_limb={}", p.qs.len(), p.lay.nf / 4, p.lay.bw - BAT0, p.rels.len());
    let te = Instant::now();
    let (cert, info) = emit(&p);
    let t_emit = te.elapsed().as_secs_f64();
    println!(
        "R1CERT_EMIT {label} ok={} fail={:?} rank_R={} qprime_entries={} qprime_lanes_used={} rel_rank={} V_G_rank={} G_pivots={} lift_ranks={:?} t_lifts={:.3} t_qprime={:.3} t_bcond={:.3} emit_seconds={t_emit:.3} pub_seconds={t_pub:.3}",
        cert.is_some(), info.fail, info.rank_r, info.qp_entries, info.qp_lanes_used, info.rel_rank, info.vg_rank, info.g_piv, info.lift_ranks, info.t_lifts, info.t_qprime, info.t_bcond
    );
    let Some(cert) = cert else {
        println!("R1CERT_RESULT {label} P_chk=false reason=no_certificate (fail closed)");
        return;
    };
    let lim = cert.limbs();
    println!(
        "R1CERT_SIZE {label} limbs={lim} bytes={} qprime_Y={}x{} qprime_kernel_limbs={} bcond_U={}x{} free={} G_entries={} G_pivots={} lifts_limbs={}",
        4 * lim,
        cert.qp_y.len(),
        cert.qp_y[0].len(),
        cert.qp.iter().map(|l| l.piv.len() + l.ents.iter().map(|(_, c)| 1 + c.len()).sum::<usize>()).sum::<usize>(),
        cert.bc_u.len(),
        cert.bc_u.first().map(|r| r.len()).unwrap_or(0),
        cert.bc_fr.len(),
        cert.bc_g.ents.len(),
        cert.bc_g.piv.len(),
        cert.lifts.iter().map(|l| l.sel.len() + l.uinv.len() * l.uinv.len()).sum::<usize>()
    );
    // The checker rebuilds the public data itself from the challenges.
    let tc = Instant::now();
    let p2 = build_pub(&s, v, &qspec, gi);
    let t_pub2 = tc.elapsed().as_secs_f64();
    let mut tm = CheckTimes::default();
    let (ok, why) = check(&p2, &cert, &mut tm);
    let t_check = tc.elapsed().as_secs_f64();
    println!(
        "R1CERT_CHECK {label} check={ok} step={why} check_seconds={t_check:.3} pub_seconds={t_pub2:.3} sources={:.3} lifts={:.3} qprime={:.3} bcond={:.3}",
        tm.src, tm.lifts, tm.qprime, tm.bcond
    );
    println!("R1CERT_RESULT {label} P_chk={ok}");
    if teeth {
        let mut rejected = 0;
        let cs = corruptions(&cert);
        let n = cs.len();
        for (name, x) in cs {
            let mut tm = CheckTimes::default();
            let (ok, why) = check(&p2, &x, &mut tm);
            if !ok {
                rejected += 1;
            }
            println!("R1CERT_TEETH {label} corruption={name:?} check={ok} step={why}");
        }
        println!("R1CERT_TEETH_SUMMARY {label} rejected={rejected}/{n}");
    }
    if args.iter().any(|x| x == "--c3diff") {
        z9d::run(&p2, &cert, &label, teeth);
    }
    println!("R1CERT_DONE {label} wall_seconds={:.3}", t0.elapsed().as_secs_f64());
}

#[path = "z9d.rs"]
pub(crate) mod z9d;
