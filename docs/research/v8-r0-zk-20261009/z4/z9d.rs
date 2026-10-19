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
}
fn family(ln: &Lanes, lks: &[&LaneKer], lane_ix: &dyn Fn(u32) -> u32) -> Option<Fam> {
    let mut f = Fam { srcs: vec![], ej: vec![], es: vec![], epo: vec![], eco: vec![], pidx: vec![], coef: vec![], ccs: vec![] };
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
        }
        for (j, cc) in &l.ents {
            if *j as usize >= ln.count(li) {
                return None;
            }
            f.ej.push(f.srcs.len() as u32);
            f.srcs.push((lane_ix(l.lane), src3(ln, li, *j as usize)));
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
    let mut tag = vec![u32::MAX; bwr];
    for (a, &pc) in c.bc_piv.iter().enumerate() {
        *tag.get_mut(pc as usize)? = 2 * a as u32;
    }
    for (f, &fc) in c.bc_fr.iter().enumerate() {
        *tag.get_mut(fc as usize)? = 2 * f as u32 + 1;
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
            } else if tag[t] != u32::MAX && tag[t] % 2 == 0 {
                negm(e[(tag[t] / 2) as usize * bwr + fc as usize])
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
        nsrc: nsrc as u32,
        lane: fq.srcs.iter().map(|z| z.0).collect(),
        wl: (0..LANES).map(|li| own_width(li) as u32).collect(),
        os: OS as u32,
        own,
        round,
        tq,
        q: q as u32,
        rel,
        ngs: ngs as u32,
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
        piv: c.bc_piv.clone(),
        fr: c.bc_fr.clone(),
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

pub(super) fn run(p: &Pub, cert: &Cert, label: &str, teeth: bool) {
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
        e: c.e.clone(), piv: c.piv.clone(), fr: c.fr.clone(), tag: c.tag.clone(), mg: c.mg, gej: c.gej.clone(),
        ges: c.ges.clone(), gepo: c.gepo.clone(), geco: c.geco.clone(), gpidx: c.gpidx.clone(), gcoef: c.gcoef.clone(),
        beta: c.beta.clone(), yg: c.yg.clone(), nm: c.nm.clone(), lu: c.lu.clone(), lid: c.lid.clone(),
    };
    let mut x = cl(&cc); bump(&mut x.rho, 1000); extra.push(("rho entry", x));
    let mut x = cl(&cc); bump(&mut x.e, 777); extra.push(("E entry", x));
    let mut x = cl(&cc); let t0 = x.tag[0]; x.tag[0] = t0 ^ 2; extra.push(("tag entry", x));
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
