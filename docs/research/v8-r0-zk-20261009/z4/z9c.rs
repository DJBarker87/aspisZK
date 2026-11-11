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
    // pv-rw-d: index loop over min(len) (the former iter_mut().zip(b)).
    let n = if v.len() < b.len() { v.len() } else { b.len() };
    let mut i = 0;
    while i < n {
        v[i] = subm(v[i], mulm(s, b[i]));
        i += 1;
    }
}
fn scale_in(v: &mut [u32], s: u32) {
    let mut i = 0;
    while i < v.len() {
        v[i] = mulm(v[i], s);
        i += 1;
    }
}
fn u(v: &[M31]) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::with_capacity(v.len());
    let mut i = 0;
    while i < v.len() {
        out.push(v[i].0);
        i += 1;
    }
    out
}
/// Row-major transpose of `cols` (each of length `h`) into `h` rows of length cols.len().
fn transpose(cols: &[&[u32]], h: usize) -> Vec<Vec<u32>> {
    (0..h).map(|t| cols.iter().map(|c| c[t]).collect()).collect()
}
/// pv-rw-d: `transpose` on owned columns, as loops (same output).
fn transpose_owned(cols: &[Vec<u32>], h: usize) -> Vec<Vec<u32>> {
    let mut out: Vec<Vec<u32>> = Vec::with_capacity(h);
    let mut t = 0;
    while t < h {
        let mut row: Vec<u32> = Vec::with_capacity(cols.len());
        let mut c = 0;
        while c < cols.len() {
            row.push(cols[c][t]);
            c += 1;
        }
        out.push(row);
        t += 1;
    }
    out
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
    /// a new pivot takes the next pivot index.  pv-rw-d: the reduction loop is
    /// `reduce_new` (stops at the first nonzero coordinate without a pivot);
    /// the new row is stored after the loop (moving v/t inside it failed:
    /// "There should be no bottoms in the value").  Same arithmetic, same order.
    fn insert(&mut self, v: Vec<u32>) -> Ins {
        let me = self.rows.len();
        let mut t = vec![0u32; me + 1];
        t[me] = 1;
        let (v, t, pos) = self.reduce_new(v, t);
        if pos < v.len() {
            let (v, t) = normalize_at(v, t, pos);
            self.piv[pos] = Some(me);
            self.rows.push((v, t));
            self.cols.push(pos);
            Ins::Pivot
        } else {
            // v reduced to 0: t[me] = 1 and 0 = v + sum_{p<me} t_p row-sources.
            let mut t = t;
            t.truncate(me);
            Ins::Zero(t)
        }
    }
    /// Reduce v (and its tag t) by the existing pivots up to the first nonzero
    /// coordinate that has no pivot; returns its index, or v.len() if none.
    fn reduce_new(&self, v: Vec<u32>, t: Vec<u32>) -> (Vec<u32>, Vec<u32>, usize) {
        reduce_new_on(&self.piv, &self.rows, v, t)
    }
    /// Reduce v; Some(y) with v = sum_k y_k (inserted pivot vector k) if v is in the span.
    /// pv-rw-d: flag loop (the former `?` inside the loop).
    fn express(&self, v: Vec<u32>) -> Option<Vec<u32>> {
        express_on(&self.piv, &self.rows, v)
    }

}
/// pv-rw-d: TagEch reduction on slices; the loop body is one step call
/// (loops through `self` fields crashed 1991 / failed "match contexts").
fn reduce_new_on(piv: &[Option<usize>], rows: &[(Vec<u32>, Vec<u32>)], v: Vec<u32>, t: Vec<u32>) -> (Vec<u32>, Vec<u32>, usize) {
    let n = v.len();
    let mut v = v;
    let mut t = t;
    let mut pos = n;
    let mut i = 0;
    while i < n && pos == n {
        let (v2, t2, new) = reduce_step(piv, rows, v, t, i, piv_at(piv, i));
        v = v2;
        t = t2;
        if new {
            pos = i;
        }
        i += 1;
    }
    (v, t, pos)
}
/// Coordinate i: zero -> nothing; pivot k -> reduce by row k; no pivot -> new pivot (true).
/// pv-rw-d: piv[i] copied out by value (matching through the borrowed array
/// failed: "Not allowed to expand enumerations with several variants").
fn piv_at(piv: &[Option<usize>], i: usize) -> Option<usize> {
    piv[i]
}
fn reduce_step(_piv: &[Option<usize>], rows: &[(Vec<u32>, Vec<u32>)], v: Vec<u32>, t: Vec<u32>, i: usize, pk: Option<usize>) -> (Vec<u32>, Vec<u32>, bool) {
    if v[i] == 0 {
        return (v, t, false);
    }
    match pk {
        Some(k) => {
            let (v, t) = reduce_with(v, t, i, &rows[k].0, &rows[k].1);
            (v, t, false)
        }
        None => (v, t, true),
    }
}
/// pv-rw-d: TagEch::express on the slices.
fn express_on(piv: &[Option<usize>], rows: &[(Vec<u32>, Vec<u32>)], v: Vec<u32>) -> Option<Vec<u32>> {
    let y = vec![0u32; rows.len()];
    match express_loop_on(piv, rows, v, y) {
        (true, y) => Some(y),
        (false, _) => None,
    }
}
fn express_loop_on(piv: &[Option<usize>], rows: &[(Vec<u32>, Vec<u32>)], v: Vec<u32>, y: Vec<u32>) -> (bool, Vec<u32>) {
    let n = v.len();
    let mut v = v;
    let mut y = y;
    let mut ok = true;
    let mut i = 0;
    while i < n && ok {
        let (v2, y2, ok2) = express_step(rows, v, y, i, piv_at(piv, i));
        v = v2;
        y = y2;
        ok = ok2;
        i += 1;
    }
    (ok, y)
}
/// Coordinate i: zero -> nothing; pivot k -> v -= s row_k, y += s tag_k; no pivot -> not in span (false).
fn express_step(rows: &[(Vec<u32>, Vec<u32>)], v: Vec<u32>, y: Vec<u32>, i: usize, pk: Option<usize>) -> (Vec<u32>, Vec<u32>, bool) {
    if v[i] == 0 {
        return (v, y, true);
    }
    match pk {
        None => (v, y, false),
        Some(k) => {
            let s = v[i];
            let v = sub_row_from(v, i, s, &rows[k].0);
            // v_old = s * row_k + v_new, row_k = sum bt_e src_e
            let y = add_tags(y, s, &rows[k].1);
            (v, y, true)
        }
    }
}
/// pv-rw-d: v[i..] -= s b[i..]; t[..bt.len()] -= s bt (the former in-loop pivot step).
fn reduce_with(mut v: Vec<u32>, mut t: Vec<u32>, i: usize, b: &[u32], bt: &[u32]) -> (Vec<u32>, Vec<u32>) {
    let s = v[i];
    axpy_sub(&mut v[i..], s, &b[i..]);
    axpy_sub(&mut t[..bt.len()], s, bt);
    (v, t)
}
/// pv-rw-d: scale v[i..] and t by 1 / v[i] (the former new-pivot step).
fn normalize_at(mut v: Vec<u32>, mut t: Vec<u32>, i: usize) -> (Vec<u32>, Vec<u32>) {
    let inv = invm(v[i]);
    scale_in(&mut v[i..], inv);
    scale_in(&mut t, inv);
    (v, t)
}
fn sub_row_from(mut v: Vec<u32>, i: usize, s: u32, b: &[u32]) -> Vec<u32> {
    axpy_sub(&mut v[i..], s, &b[i..]);
    v
}
fn add_tags(mut y: Vec<u32>, s: u32, bt: &[u32]) -> Vec<u32> {
    let mut e = 0;
    while e < bt.len() {
        y[e] = addm(y[e], mulm(s, bt[e]));
        e += 1;
    }
    y
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
    // pv-rw-d: index loop (former map closure).
    let mut out: Vec<Vec<u32>> = Vec::with_capacity(RW);
    let mut i = 0;
    while i < RW {
        out.push(chain_target(a, i));
        i += 1;
    }
    out
}
fn chain_target(a: &[QM31; 10], i: usize) -> Vec<u32> {
    let mut e = vec![M31::ZERO; RW];
    e[i] = M31::ONE;
    let q = unflat(&e);
    let ph = final_value(&q, a);
    u(&flatten(&normalize_d(&q, ph, a).expect("HalfOK")))
}
/// Lift sources: (C1 lane c < 16) eligible rows r != 1023 balanced at 1023, F lane obs;
/// (c = 16, H1) inactive rows r >= 1, 4 tower limbs, balanced at 0, K4 obs.
fn lift_src(cx: &Ctx, c: usize, idx: u32) -> Vec<u32> {
    if c < 16 {
        let r = idx as usize;
        // pv-rw-d: from-index-1 helpers instead of [1..] sub-slices of nested fields (crashed 1991).
        lift_src_c1(&cx.br, r, inactive(r))
    } else {
        let (r, k) = (idx as usize / 4, idx as usize % 4);
        let g = lift_src_h1(&cx.gr, r, inactive(r));
        u(&flatten(&scale(&g, tower(k))))
    }
}
/// pv-rw-d: the C1 source of row r: u(br[r][1..] - br[1023][1..]) if inactive,
/// else u(br[r][1..]); rows addressed by index (branch-joined row borrows crashed 1991).
fn lift_src_c1(br: &[Vec<M31>], r: usize, ia: bool) -> Vec<u32> {
    if ia {
        tail_diff_u_at(br, r, 1023)
    } else {
        tail_u_at(br, r)
    }
}
/// The H1 row of r before scaling: gr[r][1..] - gr[0][1..] if inactive, else gr[r][1..].
fn lift_src_h1(gr: &[Vec<QM31>], r: usize, ia: bool) -> Vec<QM31> {
    if ia {
        tail_diff_q_at(gr, r, 0)
    } else {
        tail_q_at(gr, r)
    }
}
fn tail_u_at(rows: &[Vec<M31>], r: usize) -> Vec<u32> {
    tail_u(&rows[r])
}
fn tail_diff_u_at(rows: &[Vec<M31>], r: usize, z: usize) -> Vec<u32> {
    tail_diff_u(&rows[r], &rows[z])
}
fn tail_q_at(rows: &[Vec<QM31>], r: usize) -> Vec<QM31> {
    tail_q(&rows[r])
}
fn tail_diff_q_at(rows: &[Vec<QM31>], r: usize, z: usize) -> Vec<QM31> {
    tail_diff_q(&rows[r], &rows[z])
}
/// u(&a[1..]) as a loop from index 1 (a.len() == 0 panics, as the slice did).
fn tail_u(a: &[M31]) -> Vec<u32> {
    assert!(1 <= a.len());
    let mut out: Vec<u32> = Vec::with_capacity(a.len() - 1);
    let mut i = 1;
    while i < a.len() {
        out.push(a[i].0);
        i += 1;
    }
    out
}
/// u(&sub_m31s(&a[1..], &b[1..])) (zip semantics: the shorter tail).
fn tail_diff_u(a: &[M31], b: &[M31]) -> Vec<u32> {
    assert!(1 <= a.len() && 1 <= b.len());
    let n = if a.len() < b.len() { a.len() } else { b.len() };
    let mut out: Vec<u32> = Vec::with_capacity(n - 1);
    let mut i = 1;
    while i < n {
        out.push(a[i].sub(b[i]).0);
        i += 1;
    }
    out
}
/// a[1..].to_vec().
fn tail_q(a: &[QM31]) -> Vec<QM31> {
    assert!(1 <= a.len());
    let mut out: Vec<QM31> = Vec::with_capacity(a.len() - 1);
    let mut i = 1;
    while i < a.len() {
        out.push(a[i]);
        i += 1;
    }
    out
}
/// sub_qm31s(&a[1..], &b[1..]).
fn tail_diff_q(a: &[QM31], b: &[QM31]) -> Vec<QM31> {
    assert!(1 <= a.len() && 1 <= b.len());
    let n = if a.len() < b.len() { a.len() } else { b.len() };
    let mut out: Vec<QM31> = Vec::with_capacity(n - 1);
    let mut i = 1;
    while i < n {
        out.push(a[i].sub(b[i]));
        i += 1;
    }
    out
}
fn lift_members(c: usize) -> Vec<u32> {
    // pv-rw-d: index loops (former filter/map/flat_map closures), same order.
    let mut out: Vec<u32> = Vec::new();
    if c < 16 {
        let mut r = 0;
        while r < N {
            if r != 1023 && eligible(c, r) {
                out.push(r as u32);
            }
            r += 1;
        }
    } else {
        let mut r = 1;
        while r < N {
            if inactive(r) {
                out.push((4 * r) as u32);
                out.push((4 * r + 1) as u32);
                out.push((4 * r + 2) as u32);
                out.push((4 * r + 3) as u32);
            }
            r += 1;
        }
    }
    out
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
    // pv-rw-d: array literal (former array map closure).
    let l = limbs(x);
    [l[0].0, l[1].0, l[2].0, l[3].0]
}

/// Gauss-Jordan inverse of a square matrix (producer side).
fn invert(m: &[Vec<u32>]) -> Option<Vec<Vec<u32>>> {
    // pv-rw-d: index loops (former enumerate/map/extend/find/into_iter chains).
    let n = m.len();
    let mut a: Vec<Vec<u32>> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        let mut x = m[i].clone();
        let mut j = 0;
        while j < n {
            x.push((i == j) as u32);
            j += 1;
        }
        a.push(x);
        i += 1;
    }
    let mut c = 0;
    while c < n {
        let mut p = c;
        while p < n && a[p][c] == 0 {
            p += 1;
        }
        if p == n {
            return None;
        }
        a.swap(c, p);
        let inv = invm(a[c][c]);
        scale_in(&mut a[c], inv);
        let pr = a[c].clone();
        let mut i = 0;
        while i < n {
            if i != c && a[i][c] != 0 {
                let s = a[i][c];
                axpy_sub(&mut a[i], s, &pr);
            }
            i += 1;
        }
        c += 1;
    }
    let mut out: Vec<Vec<u32>> = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        out.push(a[i][n..].to_vec());
        i += 1;
    }
    Some(out)
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
/// pv-rw-d: `emit`'s refusal reasons (the strings of `EmitInfo::fail`).
#[derive(Clone, Copy, Debug)]
enum EmitFail {
    HalfOk,
    LiftRank,
    QPrime,
    BCondG,
    QueryCard,
}
impl EmitFail {
    fn label(self) -> &'static str {
        match self {
            EmitFail::HalfOk => "HalfOK",
            EmitFail::LiftRank => "lift rank below width",
            EmitFail::QPrime => "QPrime_R1",
            EmitFail::BCondG => "BCondG_R1",
            EmitFail::QueryCard => "QueryCard",
        }
    }
}
/// pv-rw-d: the pure part of `EmitInfo` (no strings, no timings).
struct EmitStats {
    rank_r: usize,
    qp_entries: usize,
    qp_lanes_used: usize,
    rel_rank: usize,
    vg_rank: usize,
    g_piv: usize,
    lift_ranks: Vec<usize>,
    fail: Option<EmitFail>,
}
/// pv-rw-d: `emit`'s timing points (lifts, QPrime, BCondG).  The core uses
/// `NoLaps`; the diagnostic `emit` uses `WallLaps`.
trait Laps {
    fn start(&mut self);
    fn lap(&mut self, phase: usize);
}
struct NoLaps;
impl Laps for NoLaps {
    fn start(&mut self) {}
    fn lap(&mut self, _phase: usize) {}
}
struct WallLaps {
    tt: Instant,
    t: [f64; 3],
}
impl Laps for WallLaps {
    fn start(&mut self) {
        self.tt = Instant::now();
    }
    fn lap(&mut self, phase: usize) {
        self.t[phase] = self.tt.elapsed().as_secs_f64();
    }
}
/// The producer with its diagnostics record (strings and wall-clock laps), as
/// before; the computation is `emit_with`.
fn emit(p: &Pub) -> (Option<Cert>, EmitInfo) {
    let mut laps = WallLaps { tt: Instant::now(), t: [0.0; 3] };
    let (cert, s) = emit_with(p, z5::transport(), &mut laps);
    let info = EmitInfo {
        rank_r: s.rank_r,
        qp_entries: s.qp_entries,
        qp_lanes_used: s.qp_lanes_used,
        rel_rank: s.rel_rank,
        vg_rank: s.vg_rank,
        g_piv: s.g_piv,
        lift_ranks: s.lift_ranks,
        fail: s.fail.map(EmitFail::label),
        t_lifts: laps.t[0],
        t_qprime: laps.t[1],
        t_bcond: laps.t[2],
    };
    (cert, info)
}
/// pv-rw-d: lift `c` of the certificate (one iteration of `emit`'s lift loop).
/// Err(rank) when fewer than `w` members are independent.
fn emit_lift(cx: &Ctx, c: usize) -> Result<Lift, usize> {
    let w = lift_width(c);
    let mut e = TagEch::new(w);
    let mut sel: Vec<u32> = Vec::new();
    let members = lift_members(c);
    let mut i = 0;
    while i < members.len() {
        let m = members[i];
        if let Ins::Pivot = e.insert(lift_src(cx, c, m)) {
            sel.push(m);
            if sel.len() == w {
                break;
            }
        }
        i += 1;
    }
    if sel.len() < w {
        return Err(sel.len());
    }
    // O_S: column t = obs(src sel[t]); O_S * U = I  <=>  U = O_S^-1.
    let mut cols: Vec<Vec<u32>> = Vec::new();
    let mut t = 0;
    while t < sel.len() {
        cols.push(lift_src(cx, c, sel[t]));
        t += 1;
    }
    let os = transpose_owned(&cols, w);
    let uinv = invert(&os).expect("selected columns are independent");
    Ok(Lift { sel, uinv })
}
/// pv-rw-d: `targets.iter().map(|b| rech.express(b.clone())).collect()` into
/// Option<Vec<_>> (first None wins), as a loop.
fn express_all(rech: &TagEch, targets: &[Vec<u32>]) -> Option<Vec<Vec<u32>>> {
    let mut out: Vec<Vec<u32>> = Vec::new();
    let mut i = 0;
    while i < targets.len() {
        match rech.express(targets[i].clone()) {
            Some(y) => out.push(y),
            None => return None,
        }
        i += 1;
    }
    Some(out)
}
/// pv-rw-d: the state of one QPrime lane.
struct LaneSt {
    own: TagEch,
    piv: Vec<u32>,
    piv_round: Vec<Vec<u32>>,
    ents: Vec<(u32, Vec<u32>)>,
}
/// One source i of lane li (by value).  Some(y) = the targets were expressed
/// after this source (the former `return (lk, Some(y))`).
fn qlane_step(ln: &Lanes, li: usize, i: usize, rech: &mut TagEch, targets: &[Vec<u32>], st: LaneSt) -> (LaneSt, Option<Vec<Vec<u32>>>) {
    let mut st = st;
    let s = src3(ln, li, i);
    match st.own.insert(s.own.clone()) {
        Ins::Pivot => {
            st.piv.push(i as u32);
            st.piv_round.push(s.round);
            (st, None)
        }
        Ins::Zero(t) => {
            let c = kernel_coeffs(t);
            // rho = round_j + sum c_p round_p
            let rho = reduce_bat(s.round.clone(), &c, &st.piv_round);
            match rech.insert(rho) {
                Ins::Pivot => {
                    st.ents.push((i as u32, c));
                    if rech.rank() >= 1080 {
                        let y = express_all(rech, targets);
                        (st, y)
                    } else {
                        (st, None)
                    }
                }
                Ins::Zero(_) => (st, None),
            }
        }
    }
}
/// pv-rw-d: one lane of `emit`'s QPrime loop.  Returns the lane kernel and
/// `Some(y)` when the target expression succeeded inside this lane (the
/// original `break 'lanes`).  Step function by value, `done` flag.
fn emit_qprime_lane(ln: &Lanes, li: usize, rech: &mut TagEch, targets: &[Vec<u32>]) -> (LaneKer, Option<Vec<Vec<u32>>>) {
    let mut st = LaneSt { own: TagEch::new(own_width(li)), piv: Vec::new(), piv_round: Vec::new(), ents: Vec::new() };
    let mut y: Option<Vec<Vec<u32>>> = None;
    let mut done = false;
    let count = ln.count(li);
    let mut i = 0;
    while i < count && !done {
        let (st2, yy) = qlane_step(ln, li, i, rech, targets, st);
        st = st2;
        match yy {
            Some(v) => {
                y = Some(v);
                done = true;
            }
            None => {}
        }
        i += 1;
    }
    (LaneKer { lane: li as u32, piv: st.piv, ents: st.ents }, y)
}
/// pv-rw-d: emit's lift stage (17 lifts in order).  None after the failing
/// lift's rank was recorded.
fn emit_lifts(cx: &Ctx, info: &mut EmitStats) -> Option<Vec<Lift>> {
    let mut lifts: Vec<Lift> = Vec::new();
    let mut c = 0;
    while c < 17 {
        match emit_lift(cx, c) {
            Ok(l) => {
                info.lift_ranks.push(l.sel.len());
                lifts.push(l);
            }
            Err(rank) => {
                info.lift_ranks.push(rank);
                return None;
            }
        }
        c += 1;
    }
    Some(lifts)
}
/// pv-rw-d: emit's QPrime stage: kept lane kernels and the target expression
/// (inside a lane, else after all lanes).  Records rank_r.
/// One lane of the QPrime loop: kept by value, the echelon by &mut; Some(y) =
/// the targets were expressed in this lane (stop).
fn emit_qprime_step(ln: &Lanes, li: usize, targets: &[Vec<u32>], rech: &mut TagEch, kept: Vec<LaneKer>) -> (Vec<LaneKer>, Option<Vec<Vec<u32>>>) {
    let mut kept = kept;
    let (lk, y) = emit_qprime_lane(ln, li, rech, targets);
    match y {
        Some(y) => {
            kept.push(lk);
            (kept, Some(y))
        }
        None => {
            if lk.ents.len() != 0 {
                kept.push(lk);
            }
            (kept, None)
        }
    }
}
/// pv-rw-d: returns (kept, target expression, rank of R); the caller records
/// the rank (writing `info` here failed "Inconsistent state").
fn emit_qprime(ln: &Lanes, targets: &[Vec<u32>]) -> (Vec<LaneKer>, Option<Vec<Vec<u32>>>, usize) {
    let mut rech = TagEch::new(RW);
    let (kept, qp_y) = emit_qprime_lanes(ln, targets, &mut rech);
    let rank = rech.rank();
    let qp_y = targets_or_retry(&rech, targets, qp_y);
    (kept, qp_y, rank)
}
/// The in-lane expression if any, else one more attempt on the final echelon.
fn targets_or_retry(rech: &TagEch, targets: &[Vec<u32>], qp_y: Option<Vec<Vec<u32>>>) -> Option<Vec<Vec<u32>>> {
    match qp_y {
        Some(y) => Some(y),
        None => express_all(rech, targets),
    }
}
/// pv-rw-d: the lane loop unrolled over the 12 lanes (LANES = 12; lane C
/// pattern A5).  A lane is processed only while no lane has expressed the
/// targets yet (the former `break`); the loop forms failed "match contexts".
fn emit_qprime_lanes(ln: &Lanes, targets: &[Vec<u32>], rech: &mut TagEch) -> (Vec<LaneKer>, Option<Vec<Vec<u32>>>) {
    let st: (Vec<LaneKer>, Option<Vec<Vec<u32>>>) = (Vec::new(), None);
    let st = qp_lane_if(ln, 0, targets, rech, st);
    let st = qp_lane_if(ln, 1, targets, rech, st);
    let st = qp_lane_if(ln, 2, targets, rech, st);
    let st = qp_lane_if(ln, 3, targets, rech, st);
    let st = qp_lane_if(ln, 4, targets, rech, st);
    let st = qp_lane_if(ln, 5, targets, rech, st);
    let st = qp_lane_if(ln, 6, targets, rech, st);
    let st = qp_lane_if(ln, 7, targets, rech, st);
    let st = qp_lane_if(ln, 8, targets, rech, st);
    let st = qp_lane_if(ln, 9, targets, rech, st);
    let st = qp_lane_if(ln, 10, targets, rech, st);
    qp_lane_if(ln, 11, targets, rech, st)
}
// The unrolled chain above covers exactly LANES lanes.
const _: () = assert!(LANES == 12);
fn qp_lane_if(ln: &Lanes, li: usize, targets: &[Vec<u32>], rech: &mut TagEch, st: (Vec<LaneKer>, Option<Vec<Vec<u32>>>)) -> (Vec<LaneKer>, Option<Vec<Vec<u32>>>) {
    match st.1 {
        Some(y) => (st.0, Some(y)),
        None => emit_qprime_step(ln, li, targets, rech, st.0),
    }
}
fn count_ents(kept: &[LaneKer]) -> usize {
    let mut ents = 0;
    let mut k = 0;
    while k < kept.len() {
        ents += kept[k].ents.len();
        k += 1;
    }
    ents
}
/// pv-rw-d: BCondG relation echelon and the pivot-source relation of each pivot.
fn rel_echelon(rels: &[Vec<u32>], bwr: usize) -> (TagEch, Vec<usize>) {
    let mut re = TagEch::new(bwr);
    let mut relpiv_src: Vec<usize> = Vec::new(); // which relation row each pivot came from
    let mut k = 0;
    while k < rels.len() {
        if let Ins::Pivot = re.insert(rels[k].clone()) {
            relpiv_src.push(k);
        }
        k += 1;
    }
    (re, relpiv_src)
}
/// pv-rw-d: tags over pivot-source relations mapped to all q relations
/// (rows rv, tags rt: the former Vec<(row, tag)> as two vectors).
fn rel_rows(re: &TagEch, relpiv_src: &[usize], q: usize) -> (Vec<Vec<u32>>, Vec<Vec<u32>>) {
    rel_rows_on(&re.rows, relpiv_src, q)
}
fn rel_rows_on(rows: &[(Vec<u32>, Vec<u32>)], relpiv_src: &[usize], q: usize) -> (Vec<Vec<u32>>, Vec<Vec<u32>>) {
    let mut rv: Vec<Vec<u32>> = Vec::new();
    let mut rt: Vec<Vec<u32>> = Vec::new();
    let mut k = 0;
    while k < rows.len() {
        rv.push(rows[k].0.clone());
        rt.push(map_tags(&rows[k].1, relpiv_src, q));
        k += 1;
    }
    (rv, rt)
}
/// uq[relpiv_src[e]] = t[e] over all q relations.
fn map_tags(t: &[u32], relpiv_src: &[usize], q: usize) -> Vec<u32> {
    let mut uq = vec![0u32; q];
    let mut e = 0;
    while e < t.len() {
        uq[relpiv_src[e]] = t[e];
        e += 1;
    }
    uq
}
/// pv-rw-d: back-substitution to reduced form.
fn back_substitute(rv: &mut Vec<Vec<u32>>, rt: &mut Vec<Vec<u32>>, cols: &[usize], r: usize) {
    let mut k = 0;
    while k < r {
        let ck = cols[k];
        let pv = rv[k].clone();
        let pt = rt[k].clone();
        let mut k2 = 0;
        while k2 < r {
            if k2 != k && rv[k2][ck] != 0 {
                let s = rv[k2][ck];
                axpy_sub(&mut rv[k2], s, &pv);
                axpy_sub(&mut rt[k2], s, &pt);
            }
            k2 += 1;
        }
        k += 1;
    }
}
fn to_u32s(cols: &[usize]) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::with_capacity(cols.len());
    let mut k = 0;
    while k < cols.len() {
        out.push(cols[k] as u32);
        k += 1;
    }
    out
}
fn free_cols(re: &TagEch, bwr: usize) -> Vec<u32> {
    free_cols_on(&re.piv, bwr)
}
fn is_free(piv: &[Option<usize>], c: usize) -> bool {
    match piv_at(piv, c) {
        None => true,
        Some(_) => false,
    }
}
fn free_cols_on(piv: &[Option<usize>], bwr: usize) -> Vec<u32> {
    let mut bc_fr: Vec<u32> = Vec::new();
    let mut c = 0;
    while c < bwr {
        if is_free(piv, c) {
            bc_fr.push(c as u32);
        }
        c += 1;
    }
    bc_fr
}
fn null_vectors(bc_fr: &[u32], cols: &[usize], rv: &[Vec<u32>], bwr: usize, r: usize) -> Vec<Vec<u32>> {
    let mut nvec: Vec<Vec<u32>> = Vec::new();
    let mut fi = 0;
    while fi < bc_fr.len() {
        let f = bc_fr[fi];
        let mut n = vec![0u32; bwr];
        n[f as usize] = 1;
        let mut k = 0;
        while k < r {
            n[cols[k]] = negm(rv[k][f as usize]);
            k += 1;
        }
        nvec.push(n);
        fi += 1;
    }
    nvec
}
/// pv-rw-d: the BCondG relation part: (r, bc_u, bc_piv, bc_fr, nvec).
fn emit_rel_elim(rels: &[Vec<u32>], bwr: usize) -> (usize, Vec<Vec<u32>>, Vec<u32>, Vec<u32>, Vec<Vec<u32>>) {
    let q = rels.len();
    let (re, relpiv_src) = rel_echelon(rels, bwr);
    let r = re.rank();
    let (mut rv, mut rt) = rel_rows(&re, &relpiv_src, q);
    let cols = re.cols.clone();
    back_substitute(&mut rv, &mut rt, &cols, r);
    let bc_piv = to_u32s(&cols);
    let bc_fr = free_cols(&re, bwr);
    let nvec = null_vectors(&bc_fr, &cols, &rv, bwr, r);
    (r, rt, bc_piv, bc_fr, nvec)
}
/// pv-rw-d: the V_G stage: G lane kernel of [own; round], bat images into a
/// tagged echelon, until the null vectors are expressed.  Records g_piv, vg_rank.
fn emit_vg(ln: &Lanes, nvec: &[Vec<u32>], bwr: usize, info: &mut EmitStats) -> (LaneKer, Option<Vec<Vec<u32>>>) {
    let g = 10;
    let mut zero = TagEch::new(own_width(g) + RW);
    let mut gpiv: Vec<u32> = Vec::new();
    let mut gpiv_bat: Vec<Vec<u32>> = Vec::new();
    let mut gk = LaneKer { lane: g as u32, piv: Vec::new(), ents: Vec::new() };
    let mut vech = TagEch::new(bwr);
    let mut bc_y: Option<Vec<Vec<u32>>> = None;
    let gcount = ln.count(g);
    let mut i = 0;
    while i < gcount {
        let s = src3(ln, g, i);
        let mut zv = s.own.clone();
        zv.extend_from_slice(&s.round);
        match zero.insert(zv) {
            Ins::Pivot => {
                gpiv.push(i as u32);
                gpiv_bat.push(s.bat);
            }
            Ins::Zero(c) => {
                let b = reduce_bat(s.bat.clone(), &c, &gpiv_bat);
                if let Ins::Pivot = vech.insert(b) {
                    gk.ents.push((i as u32, c));
                    if vech.rank() >= nvec.len() {
                        bc_y = express_all(&vech, nvec);
                        if let Some(_) = bc_y {
                            break;
                        }
                    }
                }
            }
        }
        i += 1;
    }
    gk.piv = gpiv;
    info.g_piv = gk.piv.len();
    info.vg_rank = vech.rank();
    if let None = bc_y {
        bc_y = express_all(&vech, nvec);
    }
    (gk, bc_y)
}
/// pv-rw-d: b = bat + sum_p c_p (-) pivot bats (the former inner enumerate loop).
fn reduce_bat(mut b: Vec<u32>, c: &[u32], gpiv_bat: &[Vec<u32>]) -> Vec<u32> {
    let mut pidx = 0;
    while pidx < c.len() {
        let cp = c[pidx];
        if cp != 0 {
            axpy_sub(&mut b, negm(cp), &gpiv_bat[pidx]);
        }
        pidx += 1;
    }
    b
}
/// The producer (pv-rw-d: the body of the former `emit`, with the transport
/// passed in, refusal reasons as `EmitFail`, timing through `L`, and each stage
/// in its own helper; same computations in the same order).
fn emit_with<L: Laps>(p: &Pub, tr: &[u16; N], laps: &mut L) -> (Option<Cert>, EmitStats) {
    let mut info = EmitStats { rank_r: 0, qp_entries: 0, qp_lanes_used: 0, rel_rank: 0, vg_rank: 0, g_piv: 0, lift_ranks: Vec::new(), fail: None };
    let a = &p.a;
    let half = QM31::from_m31(M31(2).inv());
    let hinv = match a[9].sub(half).try_inv() {
        Some(x) => ql(x),
        None => {
            info.fail = Some(EmitFail::HalfOk);
            return (None, info);
        }
    };
    let ln = Lanes::new_with(&p.cx, tr);
    // Lifts.
    laps.start();
    let lifts = match emit_lifts(&p.cx, &mut info) {
        Some(l) => l,
        None => {
            info.fail = Some(EmitFail::LiftRank);
            return (None, info);
        }
    };
    laps.lap(0);
    laps.start();
    // QPrime: per-lane own kernel vectors, round images into a tagged echelon R.
    let targets = chain_targets(a);
    let (kept, qp_y, rank_r) = emit_qprime(&ln, &targets);
    info.rank_r = rank_r;
    let qp_y = match qp_y {
        Some(y) => y,
        None => {
            info.fail = Some(EmitFail::QPrime);
            laps.lap(1);
            return (None, info);
        }
    };
    // Entry e of R (in pivot order) is the e-th kept entry in lane order (pivot order = push order).
    info.qp_entries = count_ents(&kept);
    info.qp_lanes_used = kept.len();
    laps.lap(1);
    laps.start();
    // BCondG: reduced echelon of Rel with tags.
    let bwr = p.lay.bw - BAT0;
    let (r, bc_u, bc_piv, bc_fr, nvec) = emit_rel_elim(&p.rels, bwr);
    info.rel_rank = r;
    let (gk, bc_y) = emit_vg(&ln, &nvec, bwr, &mut info);
    laps.lap(2);
    let bc_y = match bc_y {
        Some(y) => y,
        None => {
            info.fail = Some(EmitFail::BCondG);
            return (None, info);
        }
    };
    if p.qs.len() > 22 {
        info.fail = Some(EmitFail::QueryCard);
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
