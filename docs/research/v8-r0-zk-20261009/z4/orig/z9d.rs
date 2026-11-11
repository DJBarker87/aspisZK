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
    let mut v = Vec::with_capacity(m.len() * cols);
    for r in m {
        if r.len() != cols {
            return None;
        }
        v.extend_from_slice(r);
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
fn family(ln: &Lanes, lks: &[&LaneKer], lane_ix: &dyn Fn(u32) -> u32) -> Option<Fam> {
    let mut f = Fam { srcs: vec![], ej: vec![], es: vec![], epo: vec![], eco: vec![], pidx: vec![], coef: vec![], ccs: vec![], sid: vec![] };
    for l in lks {
        let li = l.lane as usize;
        if li >= LANES {
            return None;
        }
        let po = f.pidx.len() as u32;
        for &j in &l.piv {
            if j as usize >= ln.count(li) {
                return None;
            }
            f.pidx.push(f.srcs.len() as u32);
            f.srcs.push((lane_ix(l.lane), src3(ln, li, j as usize)));
            f.sid.push((l.lane, j));
        }
        for (j, cc) in &l.ents {
            if *j as usize >= ln.count(li) {
                return None;
            }
            f.ej.push(f.srcs.len() as u32);
            f.srcs.push((lane_ix(l.lane), src3(ln, li, *j as usize)));
            f.sid.push((l.lane, *j));
            f.es.push(cc.len() as u32);
            f.epo.push(po);
            f.eco.push(f.coef.len() as u32);
            f.coef.extend_from_slice(cc);
            f.ccs.push(cc.clone());
        }
    }
    Some(f)
}
/// kcoord of entry e on the field selected by `sel` (honest emitter step).
fn image(f: &Fam, e: usize, rows: usize, sel: &dyn Fn(&Src3) -> &[u32]) -> Vec<u32> {
    let j = f.ej[e] as usize;
    let po = f.epo[e] as usize;
    let cc = &f.ccs[e];
    (0..rows)
        .map(|t| {
            let mut acc = sel(&f.srcs[j].1)[t] as u64;
            for (p, c) in cc.iter().enumerate() {
                let s = f.pidx[po + p] as usize;
                let x = sel(&f.srcs[s].1)[t] as u64;
                acc = (acc + x * *c as u64 % PM) % PM;
            }
            acc as u32
        })
        .collect()
}
fn matmul(a: &[u32], b: &[u32], ni: usize, nj: usize, len: usize) -> Vec<u32> {
    let mut out = vec![0u32; ni * nj];
    for i in 0..ni {
        let row = &a[i * len..(i + 1) * len];
        let mut acc = vec![0u64; nj];
        for (p, &x) in row.iter().enumerate() {
            if x == 0 {
                continue;
            }
            let br = &b[p * nj..(p + 1) * nj];
            for j in 0..nj {
                acc[j] = (acc[j] + x as u64 * br[j] as u64) % PM;
            }
        }
        for j in 0..nj {
            out[i * nj + j] = acc[j] as u32;
        }
    }
    out
}

/// Builders + emitter supplied values.  None = the converter refuses (shape or
/// index error that z9c also rejects); counted as a reject.
fn convert(p: &Pub, c: &Cert, ln: &Lanes) -> Option<(ck::Pub, ck::Cert)> {
    let bwr = p.lay.bw - BAT0;
    // QPrime.
    let lks: Vec<&LaneKer> = c.qp.iter().collect();
    let fq = family(ln, &lks, &|l| l)?;
    for e in 0..fq.ej.len() {
        let po = fq.epo[e] as usize;
        let s = fq.es[e] as usize;
        // the prefix must stay inside this lane's pivot block (z9c "qprime shape")
        let lane = fq.srcs[fq.ej[e] as usize].0;
        if po + s > fq.pidx.len() || (0..s).any(|q| fq.srcs[fq.pidx[po + q] as usize].0 != lane) {
            return None;
        }
    }
    let nsrc = fq.srcs.len();
    let mut own = vec![0u32; nsrc * OS];
    let mut round = vec![0u32; nsrc * RW];
    for (t, (_, s)) in fq.srcs.iter().enumerate() {
        own[t * OS..t * OS + s.own.len()].copy_from_slice(&s.own);
        round[t * RW..(t + 1) * RW].copy_from_slice(&s.round);
    }
    let m = fq.ej.len();
    let mut rho = Vec::with_capacity(m * RW);
    for e in 0..m {
        rho.extend(image(&fq, e, RW, &|s| &s.round));
    }
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
    // lst = pivots ++ free columns; tag = its inverse (tag[lst[x]] = x).
    let lst: Vec<u32> = c.bc_piv.iter().chain(c.bc_fr.iter()).copied().collect();
    let mut tag = vec![u32::MAX; bwr];
    for (x, &col) in lst.iter().enumerate() {
        *tag.get_mut(col as usize)? = x as u32;
    }
    if c.bc_g.lane != 10 {
        return None;
    }
    let fg = family(ln, &[&c.bc_g], &|_| 0)?;
    for e2 in 0..fg.ej.len() {
        if fg.epo[e2] as usize + fg.es[e2] as usize > fg.pidx.len() {
            return None;
        }
    }
    let ngs = fg.srcs.len();
    let mg = fg.ej.len();
    let mut gown = vec![0u32; ngs * OS];
    let mut ground = vec![0u32; ngs * RW];
    let mut gbat = vec![0u32; ngs * bwr];
    for (t, (_, s)) in fg.srcs.iter().enumerate() {
        gown[t * OS..t * OS + s.own.len()].copy_from_slice(&s.own);
        ground[t * RW..(t + 1) * RW].copy_from_slice(&s.round);
        gbat[t * bwr..(t + 1) * bwr].copy_from_slice(&s.bat);
    }
    let mut beta = Vec::with_capacity(mg * bwr);
    for e2 in 0..mg {
        beta.extend(image(&fg, e2, bwr, &|s| &s.bat));
    }
    if c.bc_y.len() != k {
        return None;
    }
    let yg = flat(&c.bc_y, mg)?;
    let mut nm = vec![0u32; k * bwr];
    for (f, &fc) in c.bc_fr.iter().enumerate() {
        for t in 0..bwr {
            nm[f * bwr + t] = if t == fc as usize {
                1
            } else if (tag[t] as usize) < r {
                negm(e[tag[t] as usize * bwr + fc as usize])
            } else {
                0
            };
        }
    }
    // Lifts.
    if c.lifts.len() != 17 {
        return None;
    }
    let (mut lw, mut loff, mut lo, mut lu, mut lid) = (vec![], vec![], vec![], vec![], vec![]);
    for (ci, l) in c.lifts.iter().enumerate() {
        let w = lift_width(ci);
        let members = lift_members(ci);
        if l.sel.len() != w || l.uinv.len() != w || l.sel.iter().any(|mm| members.binary_search(mm).is_err()) {
            return None;
        }
        lw.push(w as u32);
        loff.push(lo.len() as u32);
        let cols: Vec<Vec<u32>> = l.sel.iter().map(|&mm| lift_src(&p.cx, ci, mm)).collect();
        for i in 0..w {
            for x in 0..w {
                lo.push(cols[x][i]);
            }
        }
        lu.extend(flat(&l.uinv, w)?);
        for i in 0..w {
            for j in 0..w {
                lid.push((i == j) as u32);
            }
        }
    }
    let nl = lw.len() as u32;
    let pb = ck::Pub {
        nq: p.qs.len() as u32,
        a9: ql(p.a[9]).to_vec(),
        rw: RW as u32,
        bw: bwr as u32,
        lane: fq.srcs.iter().map(|z| z.0).collect(),
        wl: (0..LANES).map(|li| own_width(li) as u32).collect(),
        os: OS as u32,
        own,
        round,
        tq,
        q: q as u32,
        rel,
        gw: OS as u32,
        glane: vec![0; ngs],
        gwl: vec![own_width(10) as u32],
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
    let fq = family(&ln, &lks, &|l| l).expect("family");
    let (kq, rq, lq) = desc(&fq);
    let tb = Instant::now();
    let own = aspis_r1_cert_build::fill_own(&al, &zz, &tr, &sx, &sy, &inact, &kq, &rq, &lq, kq.len(), 376, nq);
    let fg = family(&ln, &[&cert.bc_g], &|_| 0).expect("family");
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
