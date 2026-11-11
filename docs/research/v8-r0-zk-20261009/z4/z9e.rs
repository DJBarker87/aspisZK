//! Z9e (LOG D38.3, D57.3): library entry of the prover-side P_R1 check, for
//! the R1 cost-probe prover's capped retry loop and for the simulator (G-sim).
//!
//! A child module of z9d.  The enforced predicate is D49.3's
//!     P_chk := (emit succeeds) ∧ (the extracted C3 checker accepts),
//! where the checker is `aspis_r1_cert_check::check` (D57, the Aeneas-extracted
//! copy) and its public input `pb` is built by z9d's `convert` with every
//! column family that has an extracted C3 builder substituted by that
//! builder's output: ChainT0K4 targets (`fill_tq`, D59), lift observation
//! matrices (`fill_lo`, D62), own columns of the QPrime and G families
//! (`fill_own`, D64), the relR1 limb functionals (`fill_rel`, D66), and the
//! pure-round and G batched columns of the QPrime and G families
//! (`fill_round`, `fill_gbat`, D72.2: hRent, hGent, hGBent).
//!
//! The public data are rebuilt from the attempt's actual challenges
//! (alpha, z0, z1, gamma, kappa, alpha0, alpha1, queries) exactly as z9c's
//! `build_pub` does from its synthetic trials.  Nothing here prints, stores
//! or returns a challenge, a certificate or the failing conjunct: the caller
//! learns one bit and four durations.  Any panic (out-of-range index or a
//! checked-arithmetic overflow in the extracted code, or an emitter shape
//! failure) is a rejection, as the extraction models it.
use super::*;

/// The challenges P_R1 reads (D38.1): public data only.
#[derive(Clone)]
pub struct R1PublicChallenges {
    pub alpha: [QM31; 10],
    /// (x, y) of z0 and z1.
    pub z: [[QM31; 2]; 2],
    pub gamma: W,
    pub kappa: W,
    pub alpha0: W,
    pub alpha1: W,
    pub queries: Vec<u32>,
}

/// Wall-clock split of one check (seconds).
#[derive(Clone, Copy, Debug, Default)]
pub struct R1CheckTimes {
    /// Public column data from the challenges (z9c `build_pub` body).
    pub public_data: f64,
    /// Certificate emission (z9c `emit`, the unproved producer).
    pub emit: f64,
    /// `convert` plus the extracted C3 builders.
    pub builders: f64,
    /// The extracted C3 checker.
    pub check: f64,
}

/// pv-rw-d SHELL step: the process-wide z5 transport gate that the original
/// `public_data` ran first.  A different selected transport is a rejection;
/// an unselected one is set to D18.  Kept out of the pure core (static state).
fn transport_gate(pi: [u16; N]) -> bool {
    if z5::is_selected() {
        if *z5::transport() != pi {
            return false;
        }
    } else {
        z5::set_transport(pi);
    }
    true
}

/// Shell form (gate, then the pure body), for the audit entry.
fn public_data(ch: &R1PublicChallenges) -> Option<Pub> {
    let pi = d18_transport();
    if !transport_gate(pi) {
        return None;
    }
    public_data_core(ch, &pi)
}

/// CORE step 1: the original `public_data` after its transport gate, with
/// every read of the selected transport replaced by `tr` (= the D18 table,
/// which is what the gate leaves selected).
fn public_data_core(ch: &R1PublicChallenges, tr: &[u16; N]) -> Option<Pub> {
    // pv-rw-d: iterator chains and closures as index loops; materialize without
    // the function-item argument (same predicate `inactive`).
    let pi = *tr;
    let a = ch.alpha;
    let z = [Point { x: ch.z[0][0], y: ch.z[0][1] }, Point { x: ch.z[1][0], y: ch.z[1][1] }];
    let mut qs: Vec<usize> = to_usizes(&ch.queries);
    qs.sort_unstable();
    qs.dedup();
    if qs.len() != ch.queries.len() || any_out_of_range(&qs) {
        return None;
    }
    let op = Opening { gamma: ch.gamma, kappa: ch.kappa, alpha0: ch.alpha0, alpha1: ch.alpha1 };
    let lay = Lay::new(&qs);
    let (br, gr) = raw_c_with_transport(&a, &z, &qs, tr);
    let zk = [[z[0].x, z[0].y], [z[1].x, z[1].y]];
    let wts = r1::Weights::new(&a, &zk);
    let w = wts.materialize_inactive(op.kappa);
    let geo = Geo::new();
    let phi = unit_functionals(&geo, &w, &op, &lay);
    let beta = beta_rows(&phi, &pi);
    let gpow = gamma_powers(op.gamma);
    let tail = tail_rows(&a, tr);
    let cx = Ctx { a, br, gr, tail, beta, gpow, lay: Lay::new(&qs) };
    let wd = weights_design(&a, &z, op.kappa);
    let dr = design_coeffs(&wd, &op, &qs, &lay);
    let rels = design_functionals(&dr, lay.bw);
    Some(Pub { a, qs, lay, cx, rels, z, op })
}
fn to_usizes(v: &[u32]) -> Vec<usize> {
    let mut out: Vec<usize> = Vec::with_capacity(v.len());
    let mut i = 0;
    while i < v.len() {
        out.push(v[i] as usize);
        i += 1;
    }
    out
}
/// beta[r] = phi[pi[r]].
fn beta_rows(phi: &[Vec<W>], pi: &[u16; N]) -> Vec<Vec<W>> {
    let mut out: Vec<Vec<W>> = Vec::with_capacity(N);
    let mut r = 0;
    while r < N {
        out.push(phi[usize::from(pi[r])].clone());
        r += 1;
    }
    out
}
/// gamma^l, l = 0..29.
fn gamma_powers(g: W) -> Vec<W> {
    let mut out: Vec<W> = Vec::with_capacity(29);
    let mut l = 0;
    while l < 29 {
        out.push(g.pow(l as u64));
        l += 1;
    }
    out
}
fn tail_rows(a: &[QM31; 10], tr: &[u16; N]) -> Vec<Vec<QM31>> {
    let mut out: Vec<Vec<QM31>> = Vec::with_capacity(N);
    let mut r = 0;
    while r < N {
        out.push(tail_row_co(a, usize::from(tr[r])));
        r += 1;
    }
    out
}
/// relR1 functionals of s2a, s2b, s1, every circ, every line[1] relation, in that order.
fn design_functionals(dr: &DesignCoeffs, bw: usize) -> Vec<Vec<u32>> {
    let mut rels: Vec<Vec<u32>> = Vec::new();
    push_rel_functionals(&mut rels, &dr.s2a, bw);
    push_rel_functionals(&mut rels, &dr.s2b, bw);
    push_rel_functionals(&mut rels, &dr.s1, bw);
    push_rel_list(&mut rels, &dr.circ, bw);
    push_rel_list(&mut rels, &dr.line[1], bw);
    rels
}
fn push_rel_list(out: &mut Vec<Vec<u32>>, rs: &[Vec<(usize, W)>], bw: usize) {
    let mut i = 0;
    while i < rs.len() {
        push_rel_functionals(out, &rs[i], bw);
        i += 1;
    }
}
/// pv-rw-d: `qs.iter().any(|&u| u >= 1 << 18)`.
fn any_out_of_range(qs: &[usize]) -> bool {
    let mut i = 0;
    while i < qs.len() {
        if qs[i] >= 1 << 18 {
            return true;
        }
        i += 1;
    }
    false
}
/// pv-rw-d: the former `flat_map(|r| r.limb_functionals(bw)).map(|f| u(&f[BAT0..]))` for one relation.
fn push_rel_functionals(out: &mut Vec<Vec<u32>>, r: &[(usize, W)], bw: usize) {
    let fs = limb_functionals_of(r, bw);
    let mut k = 0;
    while k < fs.len() {
        out.push(u(&fs[k][BAT0..]));
        k += 1;
    }
}

/// pv-rw-d: the former local closure `desc` (lane, row + 1, limb of each referenced source).
fn fam_desc(f: &Fam) -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    // pv-rw-d: one loop per output, each on the slice (loops through f.sid crashed 1991).
    (sid_lanes(&f.sid), sid_rows(&f.sid), sid_limbs(&f.sid))
}
fn sid_lanes(sid: &[(u32, u32)]) -> Vec<u32> {
    let mut k: Vec<u32> = Vec::with_capacity(sid.len());
    let mut i = 0;
    while i < sid.len() {
        k.push(sid[i].0);
        i += 1;
    }
    k
}
fn sid_row(li: u32, j: u32) -> u32 {
    j / fam_per_row(li) + 1
}
fn sid_limb(li: u32, j: u32) -> u32 {
    j % fam_per_row(li)
}
fn sid_rows(sid: &[(u32, u32)]) -> Vec<u32> {
    let mut r: Vec<u32> = Vec::with_capacity(sid.len());
    let mut i = 0;
    while i < sid.len() {
        r.push(sid_row(sid[i].0, sid[i].1));
        i += 1;
    }
    r
}
fn sid_limbs(sid: &[(u32, u32)]) -> Vec<u32> {
    let mut l: Vec<u32> = Vec::with_capacity(sid.len());
    let mut i = 0;
    while i < sid.len() {
        l.push(sid_limb(sid[i].0, sid[i].1));
        i += 1;
    }
    l
}
/// pv-rw-d: the stored points of the 4 slots of fibre u (the former inner
/// `for slot in 0..4` with `?`, unrolled: same order, same first error).
fn query_points(u: usize) -> Option<[(u32, u32); 4]> {
    Some([slot_point(u, 0)?, slot_point(u, 1)?, slot_point(u, 2)?, slot_point(u, 3)?])
}
fn slot_point(u: usize, slot: usize) -> Option<(u32, u32)> {
    let fi = match FibreIndex::new(u) {
        Ok(x) => x,
        Err(_) => return None,
    };
    let si = match SlotIndex::new(slot) {
        Ok(x) => x,
        Err(_) => return None,
    };
    let pt = stored_point::<M31>(child_index(fi, si));
    Some((pt.x.0, pt.y.0))
}
/// pv-rw-d: the first query whose parent is v (the former iter().find(..)).
fn first_with_parent(qs: &[usize], v: usize) -> Option<usize> {
    let mut i = 0;
    while i < qs.len() {
        if qs[i] / 4 == v {
            return Some(qs[i]);
        }
        i += 1;
    }
    None
}
/// pv-rw-d: the former local closure `pr`.
fn fam_per_row(li: u32) -> u32 {
    if li < 10 { 1 } else { 4 }
}
/// pv-rw-d: the former local closure `wl` (the 8 limbs of a WideExact value).
fn wl_limbs(x: W) -> Vec<u32> {
    // pv-rw-d: unrolled (a loop over the local limb array failed: Internal error).
    let l = wlimbs(x);
    let mut out: Vec<u32> = Vec::with_capacity(8);
    out.push(l[0].0);
    out.push(l[1].0);
    out.push(l[2].0);
    out.push(l[3].0);
    out.push(l[4].0);
    out.push(l[5].0);
    out.push(l[6].0);
    out.push(l[7].0);
    out
}
/// pv-rw-d: `ql` limbs of every value, concatenated.
fn ql_all(xs: &[QM31]) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::with_capacity(4 * xs.len());
    let mut i = 0;
    while i < xs.len() {
        let l = ql(xs[i]);
        out.push(l[0]);
        out.push(l[1]);
        out.push(l[2]);
        out.push(l[3]);
        i += 1;
    }
    out
}
/// Replace every builder-produced field of `pb` by the extracted C3 builder's
/// output (the same calls as z9d `builder_diff`).  pv-rw-d: the transport is a
/// parameter; closures and iterator chains are loops; same builder calls in
/// the same order with the same arguments.
fn extracted_builders(p: &Pub, cert: &Cert, ln: &Lanes, pb: &mut ck::Pub, transport: &[u16; N]) -> Option<()> {
    // pv-rw-d: every loop over a borrowed field is a small helper on a slice
    // (lane C pattern A2); same builder calls, same arguments, same order.
    let al: Vec<u32> = ql_all(&p.a);
    pb.tq = aspis_r1_cert_build::fill_tq(&al, &cert.hinv);
    let nq = p.qs.len();
    let zz: Vec<u32> = ql_all(&[p.z[0].x, p.z[0].y, p.z[1].x, p.z[1].y]);
    let tr: Vec<u32> = transport_u32s(transport);
    let (sx, sy) = queries_xy(&p.qs)?;
    let inact: Vec<u32> = inactive_u32s();
    if cert.lifts.len() != 17 {
        return None;
    }
    let sel1 = c1_selections(&cert.lifts);
    let selh: Vec<u32> = cert.lifts[16].sel.clone();
    pb.lo = aspis_r1_cert_build::fill_lo(&al, &zz, &tr, &sx, &sy, &inact, &sel1, &selh, nq);
    let fq = family(ln, &cert.qp, false)?;
    let (kq, rq, lq) = fam_desc(&fq);
    pb.own = aspis_r1_cert_build::fill_own(&al, &zz, &tr, &sx, &sy, &inact, &kq, &rq, &lq, kq.len(), 376, nq);
    let fg = family_single(ln, &cert.bc_g, true)?;
    let (_, rg, lg) = fam_desc(&fg);
    let kg = vec![10u32; rg.len()];
    pb.gown = aspis_r1_cert_build::fill_own(&al, &zz, &tr, &sx, &sy, &inact, &kg, &rg, &lg, kg.len(), 376, nq);
    let opl = opening_limbs(&p.op);
    let ti = inverse_transport(&tr);
    let fpos = usizes_u32(&p.lay.fpos);
    let parents = query_parents(&p.qs);
    let (rk, ru, li, xs) = rel_layout(&p.qs, &parents)?;
    pb.rel = aspis_r1_cert_build::fill_rel(&al, &zz, &tr, &inact, &ti, &opl, &fpos, &rk, &ru, &li, &xs, p.lay.nf, 8 * rk.len());
    pb.round = aspis_r1_cert_build::fill_round(&al, &tr, &inact, &kq, &rq, &lq, kq.len());
    pb.ground = aspis_r1_cert_build::fill_round(&al, &tr, &inact, &kg, &rg, &lg, kg.len());
    let x18s = x18_values(&p.lay.fpos);
    pb.gbat = aspis_r1_cert_build::fill_gbat(&al, &zz, &tr, &inact, &ti, &opl, &x18s, &rg, &lg, rg.len(), p.lay.nf);
    Some(())
}
fn transport_u32s(transport: &[u16; N]) -> Vec<u32> {
    let mut tr: Vec<u32> = Vec::with_capacity(N);
    let mut r = 0;
    while r < N {
        tr.push(transport[r] as u32);
        r += 1;
    }
    tr
}
/// Stored x and y of the 4 slots of every query, in query order.
fn queries_xy(qs: &[usize]) -> Option<(Vec<u32>, Vec<u32>)> {
    let (mut sx, mut sy): (Vec<u32>, Vec<u32>) = (Vec::new(), Vec::new());
    let mut qi = 0;
    while qi < qs.len() {
        let pts = query_points(qs[qi])?;
        sx.push(pts[0].0);
        sy.push(pts[0].1);
        sx.push(pts[1].0);
        sy.push(pts[1].1);
        sx.push(pts[2].0);
        sy.push(pts[2].1);
        sx.push(pts[3].0);
        sy.push(pts[3].1);
        qi += 1;
    }
    Some((sx, sy))
}
fn inactive_u32s() -> Vec<u32> {
    let mut inact: Vec<u32> = Vec::with_capacity(N);
    let mut r = 0;
    while r < N {
        inact.push(inactive(r) as u32);
        r += 1;
    }
    inact
}
/// The selections of lifts 0..16 concatenated (lifts.len() == 17 checked by the caller).
fn c1_selections(lifts: &[Lift]) -> Vec<u32> {
    let mut sel1: Vec<u32> = Vec::new();
    let mut l = 0;
    while l < 16 {
        sel1 = append_u32s(sel1, &lifts[l].sel);
        l += 1;
    }
    sel1
}
fn append_u32s(mut a: Vec<u32>, b: &[u32]) -> Vec<u32> {
    a.extend_from_slice(b);
    a
}
fn lane_refs(qp: &[LaneKer]) -> Vec<&LaneKer> {
    let mut lks: Vec<&LaneKer> = Vec::with_capacity(qp.len());
    let mut i = 0;
    while i < qp.len() {
        lks.push(&qp[i]);
        i += 1;
    }
    lks
}
fn opening_limbs(op: &Opening) -> Vec<u32> {
    let mut opl: Vec<u32> = Vec::with_capacity(32);
    opl.extend_from_slice(&wl_limbs(op.gamma));
    opl.extend_from_slice(&wl_limbs(op.kappa));
    opl.extend_from_slice(&wl_limbs(op.alpha0));
    opl.extend_from_slice(&wl_limbs(op.alpha1));
    opl
}
/// ti[tr[r]] = r (the former enumerate loop).
fn inverse_transport(tr: &[u32]) -> Vec<u32> {
    let mut ti = vec![0u32; N];
    let mut r = 0;
    while r < tr.len() {
        ti[tr[r] as usize] = r as u32;
        r += 1;
    }
    ti
}
fn usizes_u32(v: &[usize]) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::with_capacity(v.len());
    let mut i = 0;
    while i < v.len() {
        out.push(v[i] as u32);
        i += 1;
    }
    out
}
/// Sorted distinct parents u / 4 of the queries.
fn query_parents(qs: &[usize]) -> Vec<usize> {
    let mut parents: Vec<usize> = Vec::with_capacity(qs.len());
    let mut i = 0;
    while i < qs.len() {
        parents.push(qs[i] / 4);
        i += 1;
    }
    parents.sort();
    parents.dedup();
    parents
}
/// pv-rw-d: the relR1 row layout accumulators (rk, ru, li, xs).
struct RelAcc {
    rk: Vec<u32>,
    ru: Vec<u32>,
    li: Vec<u32>,
    xs: Vec<u32>,
}
fn rel_query_row(mut a: RelAcc, u: usize) -> RelAcc {
    a.rk.push(3);
    a.ru.push(u as u32);
    a.li.push(0);
    a.li.push(0);
    a.li.push(0);
    a.xs.push(0);
    a
}
fn rel_parent_row(qs: &[usize], v: usize, mut a: RelAcc) -> Option<RelAcc> {
    a.rk.push(4);
    let u = first_with_parent(qs, v)?;
    a.ru.push(u as u32);
    let inv = line_inverse(v, 1);
    a.li.push(wl_limbs(inv[0])[0]);
    a.li.push(wl_limbs(inv[1])[0]);
    a.li.push(wl_limbs(inv[2])[0]);
    a.xs.push(x16(v).0);
    Some(a)
}
/// The relR1 row layout (rk, ru, li, xs): three fixed rows, one row per query,
/// one row per parent (former rk literal vec![0, 1, 2] and loops; by-value steps).
fn rel_layout(qs: &[usize], parents: &[usize]) -> Option<(Vec<u32>, Vec<u32>, Vec<u32>, Vec<u32>)> {
    let mut rk: Vec<u32> = Vec::new();
    rk.push(0);
    rk.push(1);
    rk.push(2);
    let mut a = RelAcc { rk, ru: vec![0u32; 3], li: vec![0u32; 9], xs: vec![0u32; 3] };
    let mut qi = 0;
    while qi < qs.len() {
        a = rel_query_row(a, qs[qi]);
        qi += 1;
    }
    let mut cur: Option<RelAcc> = Some(a);
    let mut vi = 0;
    while vi < parents.len() {
        cur = match cur {
            Some(a) => rel_parent_row(qs, parents[vi], a),
            None => None,
        };
        vi += 1;
    }
    match cur {
        Some(a) => Some((a.rk, a.ru, a.li, a.xs)),
        None => None,
    }
}
fn x18_values(fpos: &[usize]) -> Vec<u32> {
    let mut x18s: Vec<u32> = Vec::with_capacity(fpos.len());
    let mut i = 0;
    while i < fpos.len() {
        x18s.push(x18(fpos[i]).0);
        i += 1;
    }
    x18s
}

/// Audit only (LOG D72.2), never called by the prover: on one attempt's
/// challenges, the extracted round/G-round/G-batched writers against the
/// columns `convert` takes from z9c's `Lanes` (the pre-D72.2 checker input).
/// Returns [entries, mismatches] for pb.round, pb.ground and pb.gbat.
pub fn p_r1_columns_audit(ch: &R1PublicChallenges) -> Option<[[usize; 2]; 3]> {
    let p = public_data(ch)?;
    let (cert, _) = emit(&p);
    let cert = cert?;
    let ln = Lanes::new(&p.cx);
    let (pz, _) = convert(&p, &cert, &ln)?;
    let (mut pb, _) = convert(&p, &cert, &ln)?;
    extracted_builders(&p, &cert, &ln, &mut pb, z5::transport())?;
    let cmp = |a: &[u32], b: &[u32]| [a.len(), a.iter().zip(b).filter(|(x, y)| x != y).count() + a.len().abs_diff(b.len())];
    Some([cmp(&pb.round, &pz.round), cmp(&pb.ground, &pz.ground), cmp(&pb.gbat, &pz.gbat)])
}

std::thread_local! {
    static QUIET: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
static QUIET_HOOK: std::sync::Once = std::sync::Once::new();
/// A panic inside the check is a rejection; its message (an index or an
/// overflow site, which can depend on the challenges) must not reach a log.
/// The hook suppresses messages only on a thread that is inside the check.
fn install_quiet_hook() {
    QUIET_HOOK.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !QUIET.with(|q| q.get()) {
                previous(info)
            }
        }));
    });
}

// ---------------------------------------------------------------- pv-rw-d split
// The pure CORE is `p_r1_core` = `p_r1_stages::<NoClock>`.  The SHELL
// `p_r1_check` runs the transport gate and then the SAME generic
// `p_r1_stages`, instantiated with a wall clock, under the quiet panic hook
// and `catch_unwind` (a panic is a rejection, as before).  A `StageClock`
// method takes `&mut self`, returns `()` and touches only the clock, so the
// clock cannot change the verdict.

/// Stage boundaries of one check (telemetry only).
trait StageClock {
    fn start(&mut self);
    fn stop(&mut self, stage: usize);
}
/// The core's clock: does nothing.
struct NoClock;
impl StageClock for NoClock {
    fn start(&mut self) {}
    fn stop(&mut self, _stage: usize) {}
}
/// The shell's clock (std::time::Instant; never translated).
struct WallClock {
    t: Instant,
    tm: R1CheckTimes,
}
impl StageClock for WallClock {
    fn start(&mut self) {
        self.t = Instant::now();
    }
    fn stop(&mut self, stage: usize) {
        let e = self.t.elapsed().as_secs_f64();
        match stage {
            0 => self.tm.public_data = e,
            1 => self.tm.emit = e,
            2 => self.tm.builders = e,
            _ => self.tm.check = e,
        }
    }
}

/// CORE step 2: certificate emission (z9c `emit`'s producer without its
/// diagnostics record).
fn emit_core(p: &Pub, tr: &[u16; N]) -> Option<Cert> {
    emit_with(p, tr, &mut NoLaps).0
}

/// CORE step 3: `convert` plus the extracted C3 builders.
fn builders_core(p: &Pub, cert: &Cert, tr: &[u16; N]) -> Option<(ck::Pub, ck::Cert)> {
    let ln = Lanes::new_with(&p.cx, tr);
    let (mut pb, cc) = convert(p, cert, &ln)?;
    extracted_builders(p, cert, &ln, &mut pb, tr)?;
    Some((pb, cc))
}

/// The four stages of P_chk in the original order: public data, emission,
/// builders, extracted C3 checker.  Any refusal is a rejection.
fn p_r1_stages<C: StageClock>(ch: &R1PublicChallenges, clk: &mut C) -> bool {
    let tr = d18_transport();
    clk.start();
    let p = match public_data_core(ch, &tr) {
        Some(p) => p,
        None => return false,
    };
    clk.stop(0);
    clk.start();
    let cert = emit_core(&p, &tr);
    clk.stop(1);
    let cert = match cert {
        Some(c) => c,
        None => return false,
    };
    clk.start();
    let (pb, cc) = match builders_core(&p, &cert, &tr) {
        Some(x) => x,
        None => return false,
    };
    clk.stop(2);
    clk.start();
    let ok = ck::check(&pb, &cc);
    clk.stop(3);
    ok
}

/// pv-rw-d PURE CORE of P_chk: public data only, deterministic, no clock, no
/// threads, no process state.  A panic (Lean: `fail`) is a rejection.  Assumes
/// the D18 transport, which is what the shell's gate leaves selected.
pub fn p_r1_core(ch: &R1PublicChallenges) -> bool {
    p_r1_stages(ch, &mut NoClock)
}

/// P_chk on one attempt's challenges (SHELL).  Returns the verdict and the
/// timings.  verdict = transport gate passes AND `p_r1_stages` returns true
/// without panicking.
pub fn p_r1_check(ch: &R1PublicChallenges) -> (bool, R1CheckTimes) {
    install_quiet_hook();
    QUIET.with(|q| q.set(true));
    let mut clk = WallClock { t: Instant::now(), tm: R1CheckTimes::default() };
    let verdict = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| transport_gate(d18_transport()) && p_r1_stages(ch, &mut clk)));
    QUIET.with(|q| q.set(false));
    (matches!(verdict, Ok(true)), clk.tm)
}
