//! Z9d (D49.4 C3): native differential test of the extraction-friendly checker
//! (c3/check, crate aspis-r1-cert-check) against z9c's `check`.
//!
//! A child module of z9c.  `convert` plays the builders and the emitter's
//! supplied-value step: from z9c's public data and certificate it builds the
//! flat `Pub` (referenced-source columns, relR1 functionals, chain targets,
//! lift observation matrices) and the flat `Cert` (z9c's certificate plus the
//! supplied rho, E, tags, beta, n_f matrix and lift identities, each computed
//! honestly from the possibly corrupted z9c certificate).  Verdicts of both
//! checkers are compared on the honest certificate and on z9c's 8 corruptions;
//! 6 more corruptions hit the new supplied fields.  Exact arithmetic.
use super::*;
use aspis_r1_cert_check as ck;

const OS: usize = 376;

fn flat(m: &[Vec<u32>], cols: usize) -> Option<Vec<u32>> {
    // pv-rw-d: index loop (the slice-iterator loop with an early return crashed
    // Aeneas at InterpReduceCollapse.ml:1991).
    let mut v = Vec::with_capacity(m.len() * cols);
    let mut i = 0;
    while i < m.len() {
        if m[i].len() != cols {
            return None;
        }
        v.extend_from_slice(&m[i]);
        i += 1;
    }
    Some(v)
}

/// Referenced sources of a lane kernel family: per lane, its pivots, then its
/// entries' sources.  Returns (lane, src3) per source and the flat entries.
struct Fam {
    srcs: Vec<(u32, Src3)>,
    ej: Vec<u32>,
    es: Vec<u32>,
    epo: Vec<u32>,
    eco: Vec<u32>,
    pidx: Vec<u32>,
    coef: Vec<u32>,
    ccs: Vec<Vec<u32>>,
    sid: Vec<(u32, u32)>, // (lane, source index) of each referenced source
}
/// pv-rw-d: the former `lane_ix: &dyn Fn(u32) -> u32` argument was `|l| l`
/// (QPrime) or `|_| 0` (G); `g_lane` selects the second.
fn lane_ix(g_lane: bool, l: u32) -> u32 {
    if g_lane { 0 } else { l }
}
fn family(ln: &Lanes, lks: &[LaneKer], g_lane: bool) -> Option<Fam> {
    // pv-rw-d: the lane kernels as an owned-element slice (the former
    // `&[&LaneKer]`: loops reading references out of a slice of references
    // failed "already registered mapping" / "Internal error"), state by value
    // plus an `ok` flag (the loop shape of emit_qprime_lane).
    let mut f = empty_fam();
    let mut ok = true;
    let mut i = 0;
    while i < lks.len() && ok {
        let (f2, ok2) = family_lane_flag(ln, &lks[i], g_lane, f);
        f = f2;
        ok = ok2;
        i += 1;
    }
    if ok {
        Some(f)
    } else {
        None
    }
}
/// The family of one lane kernel (the former `family(ln, &[&k], g)`).
fn family_single(ln: &Lanes, k: &LaneKer, g_lane: bool) -> Option<Fam> {
    family_lane(ln, k, g_lane, empty_fam())
}
fn empty_fam() -> Fam {
    Fam { srcs: Vec::new(), ej: Vec::new(), es: Vec::new(), epo: Vec::new(), eco: Vec::new(), pidx: Vec::new(), coef: Vec::new(), ccs: Vec::new(), sid: Vec::new() }
}
/// `family_lane` returning the family in every case plus the success flag
/// (on failure the partial family is discarded by the caller, as before).
fn family_lane_flag(ln: &Lanes, l: &LaneKer, g_lane: bool, f: Fam) -> (Fam, bool) {
    match family_lane(ln, l, g_lane, f) {
        Some(f) => (f, true),
        None => (empty_fam(), false),
    }
}
/// One lane kernel of `family`: its pivots, then its entries.  None = the
/// former `return None` (lane >= LANES or a source index out of range).
fn family_lane(ln: &Lanes, l: &LaneKer, g_lane: bool, f: Fam) -> Option<Fam> {
    let li = l.lane as usize;
    if li >= LANES {
        return None;
    }
    let po = f.pidx.len() as u32;
    let f = family_pivots(ln, li, l.lane, &l.piv, g_lane, f)?;
    family_entries(ln, li, l.lane, &l.ents, po, g_lane, f)
}
fn family_pivots(ln: &Lanes, li: usize, lane: u32, piv: &[u32], g_lane: bool, f: Fam) -> Option<Fam> {
    let count = ln.count(li);
    let mut cur: Option<Fam> = Some(f);
    let mut i = 0;
    while i < piv.len() {
        cur = match cur {
            Some(f) => family_pivot(ln, li, lane, piv[i], count, g_lane, f),
            None => None,
        };
        i += 1;
    }
    cur
}
fn family_pivot(ln: &Lanes, li: usize, lane: u32, j: u32, count: usize, g_lane: bool, mut f: Fam) -> Option<Fam> {
    if j as usize >= count {
        return None;
    }
    f.pidx.push(f.srcs.len() as u32);
    f.srcs.push((lane_ix(g_lane, lane), src3(ln, li, j as usize)));
    f.sid.push((lane, j));
    Some(f)
}
fn family_entries(ln: &Lanes, li: usize, lane: u32, ents: &[(u32, Vec<u32>)], po: u32, g_lane: bool, f: Fam) -> Option<Fam> {
    let count = ln.count(li);
    let mut cur: Option<Fam> = Some(f);
    let mut i = 0;
    while i < ents.len() {
        cur = match cur {
            Some(f) => family_entry(ln, li, lane, ents[i].0, &ents[i].1, po, count, g_lane, f),
            None => None,
        };
        i += 1;
    }
    cur
}
fn family_entry(ln: &Lanes, li: usize, lane: u32, j: u32, cc: &[u32], po: u32, count: usize, g_lane: bool, mut f: Fam) -> Option<Fam> {
    if j as usize >= count {
        return None;
    }
    f.ej.push(f.srcs.len() as u32);
    f.srcs.push((lane_ix(g_lane, lane), src3(ln, li, j as usize)));
    f.sid.push((lane, j));
    f.es.push(cc.len() as u32);
    f.epo.push(po);
    f.eco.push(f.coef.len() as u32);
    f.coef.extend_from_slice(cc);
    f.ccs.push(cc.to_vec());
    Some(f)
}
/// kcoord of entry e on the field selected by `sel` (honest emitter step).
/// pv-rw-d: the former `sel: &dyn Fn(&Src3) -> &[u32]` was `|s| &s.round` or `|s| &s.bat`.
#[derive(Clone, Copy)]
enum SrcField {
    Round,
    Bat,
}
fn src_field(s: &Src3, sel: SrcField) -> &[u32] {
    match sel {
        SrcField::Round => &s.round,
        SrcField::Bat => &s.bat,
    }
}
fn image(f: &Fam, e: usize, rows: usize, sel: SrcField) -> Vec<u32> {
    image_on(&f.srcs, &f.pidx, f.ej[e] as usize, f.epo[e] as usize, &f.ccs[e], rows, sel)
}
/// pv-rw-d: `image` on slices (loops through a borrowed struct's fields failed).
fn image_on(srcs: &[(u32, Src3)], pidx: &[u32], j: usize, po: usize, cc: &[u32], rows: usize, sel: SrcField) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::with_capacity(rows);
    let mut t = 0;
    while t < rows {
        out.push(image_at(srcs, pidx, j, po, cc, sel, t));
        t += 1;
    }
    out
}
fn image_at(srcs: &[(u32, Src3)], pidx: &[u32], j: usize, po: usize, cc: &[u32], sel: SrcField, t: usize) -> u32 {
    image_acc(srcs, pidx, po, cc, sel, t, src_value(&srcs[j].1, sel, t) as u64) as u32
}
/// pv-rw-d: the accumulation loop with its seed passed in by value (lane C R5).
fn image_acc(srcs: &[(u32, Src3)], pidx: &[u32], po: usize, cc: &[u32], sel: SrcField, t: usize, seed: u64) -> u64 {
    let mut acc = seed;
    let mut p = 0;
    while p < cc.len() {
        acc = image_step(srcs, pidx, po, cc, sel, t, p, acc);
        p += 1;
    }
    acc
}
/// pv-rw-d: src_field(s, sel)[t] read by value (a match returning a slice
/// crashed 1991, as in lane C's R7).
fn src_value(s: &Src3, sel: SrcField, t: usize) -> u32 {
    match sel {
        SrcField::Round => s.round[t],
        SrcField::Bat => s.bat[t],
    }
}
fn image_step(srcs: &[(u32, Src3)], pidx: &[u32], po: usize, cc: &[u32], sel: SrcField, t: usize, p: usize, acc: u64) -> u64 {
    let s = pidx[po + p] as usize;
    let x = src_value(&srcs[s].1, sel, t) as u64;
    (acc + x * cc[p] as u64 % PM) % PM
}
fn matmul(a: &[u32], b: &[u32], ni: usize, nj: usize, len: usize) -> Vec<u32> {
    // pv-rw-d: index loops (former enumerate loop with continue); same sums mod PM.
    let mut out = vec![0u32; ni * nj];
    let mut i = 0;
    while i < ni {
        let acc = matmul_row(a, b, i, nj, len);
        let mut j = 0;
        while j < nj {
            out[i * nj + j] = acc[j] as u32;
            j += 1;
        }
        i += 1;
    }
    out
}
fn matmul_row(a: &[u32], b: &[u32], i: usize, nj: usize, len: usize) -> Vec<u64> {
    // pv-rw-d: index arithmetic instead of sub-slices (crashed 1991); the
    // former slice ranges are the asserts (same panic conditions).
    assert!((i + 1) * len <= a.len());
    let mut acc = vec![0u64; nj];
    let mut p = 0;
    while p < len {
        let x = a[i * len + p];
        if x != 0 {
            acc = axpy_acc(acc, x, b, p * nj, nj);
        }
        p += 1;
    }
    acc
}
fn axpy_acc(mut acc: Vec<u64>, x: u32, b: &[u32], off: usize, nj: usize) -> Vec<u64> {
    assert!(off + nj <= b.len());
    let mut j = 0;
    while j < nj {
        acc[j] = (acc[j] + x as u64 * b[off + j] as u64) % PM;
        j += 1;
    }
    acc
}

/// pv-rw-d: `dst[off..off + src.len()] = src` (the former copy_from_slice on a
/// range; out of range -> panic, as the slice index did).
fn put_at(dst: &mut [u32], off: usize, src: &[u32]) {
    assert!(off + src.len() <= dst.len());
    let mut i = 0;
    while i < src.len() {
        dst[off + i] = src[i];
        i += 1;
    }
}
/// pv-rw-d: `dst[off..off + len].copy_from_slice(src)`: also panics unless src.len() == len.
fn put_exact(dst: &mut [u32], off: usize, len: usize, src: &[u32]) {
    assert!(off + len <= dst.len());
    assert!(src.len() == len);
    put_at(dst, off, src);
}
/// z9c "qprime shape": every entry's prefix stays inside its lane's pivot
/// block.  pv-rw-d: on slices (lanes[i] = srcs[i].0), flag loops without early
/// exit; once a check fails no later entry is examined (as the former `return`).
fn prefix_in_lane(pidx: &[u32], lanes: &[u32], po: usize, s: usize, lane: u32) -> bool {
    let mut ok = true;
    let mut q = 0;
    while q < s {
        if ok && lanes[pidx[po + q] as usize] != lane {
            ok = false;
        }
        q += 1;
    }
    ok
}
fn qprime_shape_ok(f: &Fam) -> bool {
    let lanes = src_lanes(f);
    qprime_shape_ok_on(&f.ej, &f.epo, &f.es, &f.pidx, &lanes)
}
fn qprime_shape_ok_on(ej: &[u32], epo: &[u32], es: &[u32], pidx: &[u32], lanes: &[u32]) -> bool {
    let mut ok = true;
    let mut e = 0;
    while e < ej.len() {
        if ok {
            ok = entry_shape_ok(ej[e], epo[e], es[e], pidx, lanes);
        }
        e += 1;
    }
    ok
}
fn entry_shape_ok(ej: u32, po: u32, s: u32, pidx: &[u32], lanes: &[u32]) -> bool {
    let po = po as usize;
    let s = s as usize;
    let lane = lanes[ej as usize];
    if po + s > pidx.len() {
        false
    } else {
        prefix_in_lane(pidx, lanes, po, s, lane)
    }
}
fn g_shape_ok(f: &Fam) -> bool {
    g_shape_ok_on(&f.epo, &f.es, f.ej.len(), f.pidx.len())
}
fn g_shape_ok_on(epo: &[u32], es: &[u32], m: usize, npidx: usize) -> bool {
    let mut ok = true;
    let mut e = 0;
    while e < m {
        if ok && epo[e] as usize + es[e] as usize > npidx {
            ok = false;
        }
        e += 1;
    }
    ok
}
/// pv-rw-d: by-value accumulators (the &mut reborrows inside these loops failed
/// "Could not match the contexts").  `put_v` = put_at, `put_exact_v` = put_exact.
fn put_v(mut dst: Vec<u32>, off: usize, src: &[u32]) -> Vec<u32> {
    put_at(&mut dst, off, src);
    dst
}
fn put_exact_v(mut dst: Vec<u32>, off: usize, len: usize, src: &[u32]) -> Vec<u32> {
    put_exact(&mut dst, off, len, src);
    dst
}
fn concat_v(mut a: Vec<u32>, b: Vec<u32>) -> Vec<u32> {
    let mut i = 0;
    while i < b.len() {
        a.push(b[i]);
        i += 1;
    }
    a
}
/// own (OS per source) and round (RW per source) blocks of a family.
fn own_round_blocks(f: &Fam) -> (Vec<u32>, Vec<u32>) {
    (own_blocks(&f.srcs), round_blocks(&f.srcs))
}
fn own_blocks(srcs: &[(u32, Src3)]) -> Vec<u32> {
    let mut own = vec![0u32; srcs.len() * OS];
    let mut t = 0;
    while t < srcs.len() {
        own = put_v(own, t * OS, &srcs[t].1.own);
        t += 1;
    }
    own
}
fn round_blocks(srcs: &[(u32, Src3)]) -> Vec<u32> {
    let mut round = vec![0u32; srcs.len() * RW];
    let mut t = 0;
    while t < srcs.len() {
        round = put_exact_v(round, t * RW, RW, &srcs[t].1.round);
        t += 1;
    }
    round
}
fn bat_blocks(f: &Fam, bwr: usize) -> Vec<u32> {
    bat_blocks_on(&f.srcs, bwr)
}
fn bat_blocks_on(srcs: &[(u32, Src3)], bwr: usize) -> Vec<u32> {
    let mut bat = vec![0u32; srcs.len() * bwr];
    let mut t = 0;
    while t < srcs.len() {
        bat = put_exact_v(bat, t * bwr, bwr, &srcs[t].1.bat);
        t += 1;
    }
    bat
}
/// image(e) for every entry e, concatenated.
fn images(f: &Fam, rows: usize, sel: SrcField) -> Vec<u32> {
    images_on(&f.srcs, &f.pidx, &f.ej, &f.epo, &f.ccs, rows, sel)
}
fn images_on(srcs: &[(u32, Src3)], pidx: &[u32], ej: &[u32], epo: &[u32], ccs: &[Vec<u32>], rows: usize, sel: SrcField) -> Vec<u32> {
    let m = ej.len();
    let mut out: Vec<u32> = Vec::with_capacity(m * rows);
    let mut e = 0;
    while e < m {
        out = concat_v(out, image_on(srcs, pidx, ej[e] as usize, epo[e] as usize, &ccs[e], rows, sel));
        e += 1;
    }
    out
}
/// lst = pivots ++ free columns; tag = its inverse (tag[lst[x]] = x); None if a column is >= bwr.
fn lst_tag(piv: &[u32], fr: &[u32], bwr: usize) -> Option<(Vec<u32>, Vec<u32>)> {
    let mut lst: Vec<u32> = Vec::with_capacity(piv.len() + fr.len());
    lst.extend_from_slice(piv);
    lst.extend_from_slice(fr);
    let mut tag = vec![u32::MAX; bwr];
    let mut x = 0;
    while x < lst.len() {
        let col = lst[x] as usize;
        if col >= bwr {
            return None;
        }
        tag[col] = x as u32;
        x += 1;
    }
    Some((lst, tag))
}
fn null_matrix(fr: &[u32], tag: &[u32], e: &[u32], bwr: usize, r: usize) -> Vec<u32> {
    // pv-rw-d: one row per free column, the column passed by value.
    let mut nm: Vec<u32> = Vec::with_capacity(fr.len() * bwr);
    let mut f = 0;
    while f < fr.len() {
        nm.extend_from_slice(&null_row(tag, e, bwr, r, fr[f]));
        f += 1;
    }
    nm
}
fn null_entry(tag: &[u32], e: &[u32], bwr: usize, r: usize, fc: u32, t: usize) -> u32 {
    if t == fc as usize {
        1
    } else if (tag[t] as usize) < r {
        negm(e[tag[t] as usize * bwr + fc as usize])
    } else {
        0
    }
}
fn null_row(tag: &[u32], e: &[u32], bwr: usize, r: usize, fc: u32) -> Vec<u32> {
    let mut row: Vec<u32> = Vec::with_capacity(bwr);
    let mut t = 0;
    while t < bwr {
        row.push(null_entry(tag, e, bwr, r, fc, t));
        t += 1;
    }
    row
}
fn contains_u32(v: &[u32], x: u32) -> bool {
    let mut i = 0;
    while i < v.len() {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}
/// Selection shape of lift ci: |sel| = |uinv| = w and every selected member eligible
/// (lift_members is strictly increasing, so membership = the former binary_search Ok).
fn lift_shape_ok(l: &Lift, w: usize, members: &[u32]) -> bool {
    l.sel.len() == w && l.uinv.len() == w && all_members(&l.sel, members)
}
/// Every selected member eligible; no element is examined after the first failure.
fn all_members(sel: &[u32], members: &[u32]) -> bool {
    let mut ok = true;
    let mut i = 0;
    while i < sel.len() {
        if ok && !contains_u32(members, sel[i]) {
            ok = false;
        }
        i += 1;
    }
    ok
}
/// Observation block of lift ci, row-major over (i, x): lo[i w + x] = src(sel[x])[i],
/// appended to `lo` (by value).
fn lift_cols(cx: &Ctx, ci: usize, sel: &[u32]) -> Vec<Vec<u32>> {
    let mut cols: Vec<Vec<u32>> = Vec::with_capacity(sel.len());
    let mut x = 0;
    while x < sel.len() {
        cols.push(lift_src(cx, ci, sel[x]));
        x += 1;
    }
    cols
}
fn lift_obs_v(cols: &[Vec<u32>], w: usize, mut lo: Vec<u32>) -> Vec<u32> {
    let mut i = 0;
    while i < w {
        let mut x = 0;
        while x < w {
            lo.push(cols[x][i]);
            x += 1;
        }
        i += 1;
    }
    lo
}
fn identity_v(mut lid: Vec<u32>, w: usize) -> Vec<u32> {
    let mut i = 0;
    while i < w {
        let mut j = 0;
        while j < w {
            lid.push((i == j) as u32);
            j += 1;
        }
        i += 1;
    }
    lid
}
fn lane_kers(qp: &[LaneKer]) -> Vec<&LaneKer> {
    let mut v: Vec<&LaneKer> = Vec::with_capacity(qp.len());
    let mut i = 0;
    while i < qp.len() {
        v.push(&qp[i]);
        i += 1;
    }
    v
}
/// pv-rw-d: the lift part's accumulators.
struct LiftAcc {
    lw: Vec<u32>,
    loff: Vec<u32>,
    lo: Vec<u32>,
    lu: Vec<u32>,
    lid: Vec<u32>,
}
/// One lift of the converter (by value); None on a shape error.
fn lift_block_step(cx: &Ctx, ci: usize, l: &Lift, mut a: LiftAcc) -> Option<LiftAcc> {
    let w = lift_width(ci);
    let members = lift_members(ci);
    if !lift_shape_ok(l, w, &members) {
        return None;
    }
    a.lw.push(w as u32);
    a.loff.push(a.lo.len() as u32);
    let cols = lift_cols(cx, ci, &l.sel);
    a.lo = lift_obs_v(&cols, w, a.lo);
    let uf = flat(&l.uinv, w)?;
    a.lu = concat_v(a.lu, uf);
    a.lid = identity_v(a.lid, w);
    Some(a)
}
/// The lift part of the converter: (lw, loff, lo, lu, lid); None on a shape error.
fn lift_blocks(cx: &Ctx, lifts: &[Lift]) -> Option<(Vec<u32>, Vec<u32>, Vec<u32>, Vec<u32>, Vec<u32>)> {
    let mut cur: Option<LiftAcc> = Some(LiftAcc { lw: Vec::new(), loff: Vec::new(), lo: Vec::new(), lu: Vec::new(), lid: Vec::new() });
    let mut ci = 0;
    while ci < lifts.len() {
        cur = match cur {
            Some(a) => lift_block_step(cx, ci, &lifts[ci], a),
            None => None,
        };
        ci += 1;
    }
    match cur {
        Some(a) => Some((a.lw, a.loff, a.lo, a.lu, a.lid)),
        None => None,
    }
}
fn src_lanes(f: &Fam) -> Vec<u32> {
    src_lanes_on(&f.srcs)
}
fn src_lanes_on(srcs: &[(u32, Src3)]) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::with_capacity(srcs.len());
    let mut i = 0;
    while i < srcs.len() {
        out.push(srcs[i].0);
        i += 1;
    }
    out
}
fn lane_widths() -> Vec<u32> {
    let mut out: Vec<u32> = Vec::with_capacity(LANES);
    let mut li = 0;
    while li < LANES {
        out.push(own_width(li) as u32);
        li += 1;
    }
    out
}
/// Builders + emitter supplied values.  None = the converter refuses (shape or
/// index error that z9c also rejects); counted as a reject.  pv-rw-d: the
/// former loops and closures are helpers on slices; same checks and values in
/// the same order.
fn convert(p: &Pub, c: &Cert, ln: &Lanes) -> Option<(ck::Pub, ck::Cert)> {
    let bwr = p.lay.bw - BAT0;
    // QPrime.
    let fq = family(ln, &c.qp, false)?;
    if !qprime_shape_ok(&fq) {
        return None;
    }
    let (own, round) = own_round_blocks(&fq);
    let m = fq.ej.len();
    let rho = images(&fq, RW, SrcField::Round);
    if c.qp_y.len() != RW {
        return None;
    }
    let y = flat(&c.qp_y, m)?;
    let targets = chain_targets(&p.a);
    let tq = flat(&targets, RW)?;
    // BCondG.
    let q = p.rels.len();
    let rel = flat(&p.rels, bwr)?;
    let r = c.bc_piv.len();
    let k = c.bc_fr.len();
    if c.bc_u.len() != r {
        return None;
    }
    let u = flat(&c.bc_u, q)?;
    let e = matmul(&u, &rel, r, bwr, q);
    let (lst, tag) = lst_tag(&c.bc_piv, &c.bc_fr, bwr)?;
    if c.bc_g.lane != 10 {
        return None;
    }
    let fg = family_single(ln, &c.bc_g, true)?;
    if !g_shape_ok(&fg) {
        return None;
    }
    let ngs = fg.srcs.len();
    let mg = fg.ej.len();
    let (gown, ground) = own_round_blocks(&fg);
    let gbat = bat_blocks(&fg, bwr);
    let beta = images(&fg, bwr, SrcField::Bat);
    if c.bc_y.len() != k {
        return None;
    }
    let yg = flat(&c.bc_y, mg)?;
    let nm = null_matrix(&c.bc_fr, &tag, &e, bwr, r);
    // Lifts.
    if c.lifts.len() != 17 {
        return None;
    }
    let (lw, loff, lo, lu, lid) = lift_blocks(&p.cx, &c.lifts)?;
    let nl = lw.len() as u32;
    // pv-rw-d: was the list literal vec![own_width(10) as u32].
    let mut gwl_g: Vec<u32> = Vec::with_capacity(1);
    gwl_g.push(own_width(10) as u32);
    let pb = ck::Pub {
        nq: p.qs.len() as u32,
        a9: ql(p.a[9]).to_vec(),
        rw: RW as u32,
        bw: bwr as u32,
        lane: src_lanes(&fq),
        wl: lane_widths(),
        os: OS as u32,
        own,
        round,
        tq,
        q: q as u32,
        rel,
        gw: OS as u32,
        glane: vec![0; ngs],
        gwl: gwl_g,
        gown,
        ground,
        gbat,
        nl,
        lw,
        loff,
        lo,
    };
    let cc = ck::Cert {
        hinv: c.hinv.to_vec(),
        m: m as u32,
        ej: fq.ej,
        es: fq.es,
        epo: fq.epo,
        eco: fq.eco,
        pidx: fq.pidx,
        coef: fq.coef,
        rho,
        y,
        r: r as u32,
        k: k as u32,
        u,
        e,
        lst,
        tag,
        mg: mg as u32,
        gej: fg.ej,
        ges: fg.es,
        gepo: fg.epo,
        geco: fg.eco,
        gpidx: fg.pidx,
        gcoef: fg.coef,
        beta,
        yg,
        nm,
        lu,
        lid,
    };
    Some((pb, cc))
}

/// The new checker, panics (out-of-range index, overflow) mapped to false, as
/// the extraction maps them to failure.
fn c3_check(pb: &ck::Pub, cc: &ck::Cert) -> bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| ck::check(pb, cc))).unwrap_or(false)
}
fn c3_verdict(p: &Pub, c: &Cert, ln: &Lanes) -> (bool, f64) {
    let t = Instant::now();
    let v = match convert(p, c, ln) {
        Some((pb, cc)) => c3_check(&pb, &cc),
        None => false,
    };
    (v, t.elapsed().as_secs_f64())
}

/// Builder differential (D57.3): the extracted-copy chain targets against z9c's.
fn builder_diff(p: &Pub, cert: &Cert, label: &str) {
    let tb = Instant::now();
    let al: Vec<u32> = (0..10).flat_map(|j| ql(p.a[j])).collect();
    let tq = aspis_r1_cert_build::fill_tq(&al, &cert.hinv);
    let t_build = tb.elapsed().as_secs_f64();
    let want = flat(&chain_targets(&p.a), RW).expect("chain targets");
    let diff = tq.iter().zip(&want).filter(|(x, y)| x != y).count();
    println!("R1C3_BUILD {label} builder=chain_targets agree={} entries={} mismatches={diff} build_seconds={t_build:.3}", tq == want, tq.len());
    // Builder 2: the lift observation matrices.
    let nq = p.qs.len();
    let zz: Vec<u32> = p.z.iter().flat_map(|pt| ql(pt.x).into_iter().chain(ql(pt.y))).collect();
    let tr: Vec<u32> = z5::transport().iter().map(|&x| x as u32).collect();
    let (mut sx, mut sy) = (vec![], vec![]);
    for &u in &p.qs {
        for slot in 0..4 {
            let pt = stored_point::<M31>(child_index(FibreIndex::new(u).unwrap(), SlotIndex::new(slot).unwrap()));
            sx.push(pt.x.0);
            sy.push(pt.y.0);
        }
    }
    let inact: Vec<u32> = (0..N).map(|r| inactive(r) as u32).collect();
    let mut sel1 = vec![];
    for l in 0..16 {
        sel1.extend(cert.lifts[l].sel.iter().copied());
    }
    let selh: Vec<u32> = cert.lifts[16].sel.clone();
    let tb = Instant::now();
    let lo = aspis_r1_cert_build::fill_lo(&al, &zz, &tr, &sx, &sy, &inact, &sel1, &selh, nq);
    let t_lo = tb.elapsed().as_secs_f64();
    let mut want = vec![];
    for (ci, l) in cert.lifts.iter().enumerate() {
        let w = lift_width(ci);
        let cols: Vec<Vec<u32>> = l.sel.iter().map(|&mm| lift_src(&p.cx, ci, mm)).collect();
        for i in 0..w {
            for x in 0..w {
                want.push(cols[x][i]);
            }
        }
    }
    let diff = lo.iter().zip(&want).filter(|(x, y)| x != y).count();
    println!("R1C3_BUILD {label} builder=lift_columns agree={} entries={} want_entries={} mismatches={diff} build_seconds={t_lo:.3}", lo == want, lo.len(), want.len());
    // Builder 3: the own columns of the referenced sources (QPrime family and G family).
    let ln = Lanes::new(&p.cx);
    let (pbw, _) = convert(p, cert, &ln).expect("honest certificate converts");
    let desc = |f: &Fam| -> (Vec<u32>, Vec<u32>, Vec<u32>) {
        let pr = |li: u32| if li < 10 { 1 } else { 4 };
        (f.sid.iter().map(|&(li, _)| li).collect(), f.sid.iter().map(|&(li, j)| j / pr(li) + 1).collect(), f.sid.iter().map(|&(li, j)| j % pr(li)).collect())
    };
    let lks: Vec<&LaneKer> = cert.qp.iter().collect();
    let fq = family(&ln, &cert.qp, false).expect("family");
    let (kq, rq, lq) = desc(&fq);
    let tb = Instant::now();
    let own = aspis_r1_cert_build::fill_own(&al, &zz, &tr, &sx, &sy, &inact, &kq, &rq, &lq, kq.len(), 376, nq);
    let fg = family_single(&ln, &cert.bc_g, true).expect("family");
    let (_, rg, lg) = desc(&fg);
    let kg = vec![10u32; rg.len()];
    let gown = aspis_r1_cert_build::fill_own(&al, &zz, &tr, &sx, &sy, &inact, &kg, &rg, &lg, kg.len(), 376, nq);
    let t_own = tb.elapsed().as_secs_f64();
    let dq = own.iter().zip(&pbw.own).filter(|(x, y)| x != y).count();
    let dg = gown.iter().zip(&pbw.gown).filter(|(x, y)| x != y).count();
    println!("R1C3_BUILD {label} builder=own_columns agree={} entries={} want_entries={} mismatches={dq} sources={} build_seconds={t_own:.3}", own == pbw.own, own.len(), pbw.own.len(), kq.len());
    println!("R1C3_BUILD {label} builder=g_own_columns agree={} entries={} want_entries={} mismatches={dg} sources={}", gown == pbw.gown, gown.len(), pbw.gown.len(), kg.len());
    // Builder 4 (D64 hRel): the relR1 limb functionals.  Inputs: the openings, the inverse
    // transport, the folded positions, the relation descriptors (kind, query), the line
    // inverses (reading 1) and the stored log-16 nodes of the line relations.
    let wl = |x: W| -> Vec<u32> { wlimbs(x).iter().map(|m| m.0).collect() };
    let opl: Vec<u32> = [p.op.gamma, p.op.kappa, p.op.alpha0, p.op.alpha1].iter().flat_map(|&x| wl(x)).collect();
    let mut ti = vec![0u32; N];
    for (r, &j) in tr.iter().enumerate() {
        ti[j as usize] = r as u32;
    }
    let fpos: Vec<u32> = p.lay.fpos.iter().map(|&x| x as u32).collect();
    let mut parents: Vec<usize> = p.qs.iter().map(|u| u / 4).collect();
    parents.sort();
    parents.dedup();
    let (mut rk, mut ru, mut li, mut xs) = (vec![0u32, 1, 2], vec![0u32; 3], vec![0u32; 9], vec![0u32; 3]);
    for &u in &p.qs {
        rk.push(3);
        ru.push(u as u32);
        li.extend([0, 0, 0]);
        xs.push(0);
    }
    for &v in &parents {
        rk.push(4);
        ru.push(*p.qs.iter().find(|&&u| u / 4 == v).unwrap() as u32);
        li.extend(line_inverse(v, 1).iter().map(|&x| wl(x)[0]));
        xs.push(x16(v).0);
    }
    let tb = Instant::now();
    let rel = aspis_r1_cert_build::fill_rel(&al, &zz, &tr, &inact, &ti, &opl, &fpos, &rk, &ru, &li, &xs, p.lay.nf, 8 * rk.len());
    let t_rel = tb.elapsed().as_secs_f64();
    let want = flat(&p.rels, p.lay.bw - BAT0).expect("relations");
    let dr = rel.iter().zip(&want).filter(|(x, y)| x != y).count();
    println!("R1C3_BUILD {label} builder=relations agree={} entries={} want_entries={} mismatches={dr} relations={} build_seconds={t_rel:.3}", rel == want, rel.len(), want.len(), rk.len());
    // Builder 5 (D72.2 hRent/hGent): the pure-round columns of the QPrime and G families.
    let tb = Instant::now();
    let round = aspis_r1_cert_build::fill_round(&al, &tr, &inact, &kq, &rq, &lq, kq.len());
    let ground = aspis_r1_cert_build::fill_round(&al, &tr, &inact, &kg, &rg, &lg, kg.len());
    let t_round = tb.elapsed().as_secs_f64();
    let d5 = round.iter().zip(&pbw.round).filter(|(x, y)| x != y).count();
    let d5g = ground.iter().zip(&pbw.ground).filter(|(x, y)| x != y).count();
    println!("R1C3_BUILD {label} builder=round_columns agree={} entries={} want_entries={} mismatches={d5} sources={} build_seconds={t_round:.3}", round == pbw.round, round.len(), pbw.round.len(), kq.len());
    println!("R1C3_BUILD {label} builder=g_round_columns agree={} entries={} want_entries={} mismatches={d5g} sources={}", ground == pbw.ground, ground.len(), pbw.ground.len(), kg.len());
    // Builder 6 (D72.2 hGBent): the G batched columns; input: the stored first-line points of the folded positions.
    let x18s: Vec<u32> = p.lay.fpos.iter().map(|&f| x18(f).0).collect();
    let tb = Instant::now();
    let gbat = aspis_r1_cert_build::fill_gbat(&al, &zz, &tr, &inact, &ti, &opl, &x18s, &rg, &lg, rg.len(), p.lay.nf);
    let t_gbat = tb.elapsed().as_secs_f64();
    let d6 = gbat.iter().zip(&pbw.gbat).filter(|(x, y)| x != y).count();
    println!("R1C3_BUILD {label} builder=g_batched_columns agree={} entries={} want_entries={} mismatches={d6} sources={} build_seconds={t_gbat:.3}", gbat == pbw.gbat, gbat.len(), pbw.gbat.len(), rg.len());
    // Teeth: the comparison detects a dropped balance (inactive flags cleared) and a moved stored point.
    let flat0 = vec![0u32; N];
    let t5 = aspis_r1_cert_build::fill_round(&al, &tr, &flat0, &kq, &rq, &lq, kq.len());
    let m5 = t5.iter().zip(&pbw.round).filter(|(x, y)| x != y).count();
    let mut x18b = x18s.clone();
    x18b[0] = (x18b[0] + 1) % 0x7fff_ffff;
    let t6 = aspis_r1_cert_build::fill_gbat(&al, &zz, &tr, &inact, &ti, &opl, &x18b, &rg, &lg, rg.len(), p.lay.nf);
    let m6 = t6.iter().zip(&pbw.gbat).filter(|(x, y)| x != y).count();
    println!("R1C3_BUILD_TEETH {label} round_inactive_cleared_mismatches={m5} gbat_x18_moved_mismatches={m6}");
}

pub(super) fn run(p: &Pub, cert: &Cert, label: &str, teeth: bool) {
    builder_diff(p, cert, label);
    let ln = Lanes::new(&p.cx);
    let mut tm = CheckTimes::default();
    let (z9c_ok, why) = check(p, cert, &mut tm);
    let tc = Instant::now();
    let conv = convert(p, cert, &ln);
    let t_conv = tc.elapsed().as_secs_f64();
    let (pb, cc) = conv.expect("honest certificate converts");
    let tk = Instant::now();
    let c3_ok = c3_check(&pb, &cc);
    let t_c3 = tk.elapsed().as_secs_f64();
    println!(
        "R1C3_DIFF {label} cert=honest z9c={z9c_ok} z9c_step={why} c3={c3_ok} agree={} convert_seconds={t_conv:.3} c3_check_seconds={t_c3:.3} pub_limbs={} cert_limbs={}",
        z9c_ok == c3_ok,
        pb.a9.len() + pb.lane.len() + pb.wl.len() + pb.own.len() + pb.round.len() + pb.tq.len() + pb.rel.len() + pb.gown.len() + pb.ground.len() + pb.gbat.len() + pb.lo.len(),
        cc.ej.len() * 4 + cc.pidx.len() + cc.coef.len() + cc.rho.len() + cc.y.len() + cc.u.len() + cc.e.len() + cc.tag.len() + cc.gej.len() * 4 + cc.gpidx.len() + cc.gcoef.len() + cc.beta.len() + cc.yg.len() + cc.nm.len() + cc.lu.len() + cc.lid.len()
    );
    if !teeth {
        return;
    }
    let mut agree = 0;
    let cs = corruptions(cert);
    let n = cs.len();
    for (name, x) in cs {
        let mut tm = CheckTimes::default();
        let (z, why) = check(p, &x, &mut tm);
        let (v, t) = c3_verdict(p, &x, &ln);
        if z == v {
            agree += 1;
        }
        println!("R1C3_TEETH {label} corruption={name:?} z9c={z} z9c_step={why} c3={v} agree={} c3_seconds={t:.3}", z == v);
    }
    println!("R1C3_TEETH_SUMMARY {label} agree={agree}/{n}");
    // Corruptions of the supplied fields that z9c does not have.
    let bump = |v: &mut Vec<u32>, i: usize| v[i] = addm(v[i], 1);
    let mut extra: Vec<(&str, ck::Cert)> = vec![];
    let cl = |c: &ck::Cert| ck::Cert {
        hinv: c.hinv.clone(), m: c.m, ej: c.ej.clone(), es: c.es.clone(), epo: c.epo.clone(), eco: c.eco.clone(),
        pidx: c.pidx.clone(), coef: c.coef.clone(), rho: c.rho.clone(), y: c.y.clone(), r: c.r, k: c.k, u: c.u.clone(),
        e: c.e.clone(), lst: c.lst.clone(), tag: c.tag.clone(), mg: c.mg, gej: c.gej.clone(),
        ges: c.ges.clone(), gepo: c.gepo.clone(), geco: c.geco.clone(), gpidx: c.gpidx.clone(), gcoef: c.gcoef.clone(),
        beta: c.beta.clone(), yg: c.yg.clone(), nm: c.nm.clone(), lu: c.lu.clone(), lid: c.lid.clone(),
    };
    let mut x = cl(&cc); bump(&mut x.rho, 1000); extra.push(("rho entry", x));
    let mut x = cl(&cc); bump(&mut x.e, 777); extra.push(("E entry", x));
    let mut x = cl(&cc); x.tag.swap(0, 1); extra.push(("tag entries swapped", x));
    let mut x = cl(&cc); bump(&mut x.beta, 4321); extra.push(("beta entry", x));
    let mut x = cl(&cc); bump(&mut x.nm, 99); extra.push(("n_f matrix entry", x));
    let mut x = cl(&cc); bump(&mut x.lid, 5); extra.push(("lift identity entry", x));
    let ne = extra.len();
    let mut rej = 0;
    for (name, x) in extra {
        let v = c3_check(&pb, &x);
        if !v {
            rej += 1;
        }
        println!("R1C3_TEETH_EXTRA {label} corruption={name:?} c3={v}");
    }
    println!("R1C3_TEETH_EXTRA_SUMMARY {label} rejected={rej}/{ne}");
}

/// Library entry of the prover-side P_R1 check (D38.3), for the R1 prover.
#[path = "z9e.rs"]
pub(crate) mod z9e;
