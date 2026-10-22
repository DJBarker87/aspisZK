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

fn public_data(ch: &R1PublicChallenges) -> Option<Pub> {
    let pi = d18_transport();
    if z5::is_selected() {
        if *z5::transport() != pi {
            return None;
        }
    } else {
        z5::set_transport(pi);
    }
    let a = ch.alpha;
    let z = [Point { x: ch.z[0][0], y: ch.z[0][1] }, Point { x: ch.z[1][0], y: ch.z[1][1] }];
    let mut qs: Vec<usize> = ch.queries.iter().map(|&u| u as usize).collect();
    qs.sort_unstable();
    qs.dedup();
    if qs.len() != ch.queries.len() || qs.iter().any(|&u| u >= 1 << 18) {
        return None;
    }
    let op = Opening { gamma: ch.gamma, kappa: ch.kappa, alpha0: ch.alpha0, alpha1: ch.alpha1 };
    let lay = Lay::new(&qs);
    let (br, gr) = raw_c(&a, &z, &qs);
    let zk = [[z[0].x, z[0].y], [z[1].x, z[1].y]];
    let wts = r1::Weights::new(&a, &zk);
    let w = wts.materialize(op.kappa, inactive_fn);
    let geo = Geo::new();
    let phi = unit_functionals(&geo, &w, &op, &lay);
    let beta: Vec<Vec<W>> = (0..N).map(|r| phi[usize::from(pi[r])].clone()).collect();
    let gpow = (0..29).map(|l| op.gamma.pow(l as u64)).collect();
    let tail: Vec<_> = (0..N).map(|r| tail_row(&a, r)).collect();
    let cx = Ctx { a, br, gr, tail, beta, gpow, lay: Lay::new(&qs) };
    let wd = weights_design(&a, &z, op.kappa);
    let dr = design_relations(&wd, &op, &qs, &lay);
    let mut rl: Vec<&Rel> = vec![&dr.s2a, &dr.s2b, &dr.s1];
    rl.extend(dr.circ.iter());
    rl.extend(dr.line[1].iter());
    let rels = rl.iter().flat_map(|r| r.limb_functionals(lay.bw)).map(|f| u(&f[BAT0..])).collect();
    Some(Pub { a, qs, lay, cx, rels, z, op })
}

/// Replace every builder-produced field of `pb` by the extracted C3 builder's
/// output (the same calls as z9d `builder_diff`).
fn extracted_builders(p: &Pub, cert: &Cert, ln: &Lanes, pb: &mut ck::Pub) -> Option<()> {
    let al: Vec<u32> = (0..10).flat_map(|j| ql(p.a[j])).collect();
    pb.tq = aspis_r1_cert_build::fill_tq(&al, &cert.hinv);
    let nq = p.qs.len();
    let zz: Vec<u32> = p.z.iter().flat_map(|pt| ql(pt.x).into_iter().chain(ql(pt.y))).collect();
    let tr: Vec<u32> = z5::transport().iter().map(|&x| x as u32).collect();
    let (mut sx, mut sy) = (vec![], vec![]);
    for &u in &p.qs {
        for slot in 0..4 {
            let pt = stored_point::<M31>(child_index(FibreIndex::new(u).ok()?, SlotIndex::new(slot).ok()?));
            sx.push(pt.x.0);
            sy.push(pt.y.0);
        }
    }
    let inact: Vec<u32> = (0..N).map(|r| inactive(r) as u32).collect();
    if cert.lifts.len() != 17 {
        return None;
    }
    let mut sel1 = vec![];
    for l in 0..16 {
        sel1.extend(cert.lifts[l].sel.iter().copied());
    }
    let selh: Vec<u32> = cert.lifts[16].sel.clone();
    pb.lo = aspis_r1_cert_build::fill_lo(&al, &zz, &tr, &sx, &sy, &inact, &sel1, &selh, nq);
    let desc = |f: &Fam| -> (Vec<u32>, Vec<u32>, Vec<u32>) {
        let pr = |li: u32| if li < 10 { 1 } else { 4 };
        (
            f.sid.iter().map(|&(li, _)| li).collect(),
            f.sid.iter().map(|&(li, j)| j / pr(li) + 1).collect(),
            f.sid.iter().map(|&(li, j)| j % pr(li)).collect(),
        )
    };
    let lks: Vec<&LaneKer> = cert.qp.iter().collect();
    let fq = family(ln, &lks, &|l| l)?;
    let (kq, rq, lq) = desc(&fq);
    pb.own = aspis_r1_cert_build::fill_own(&al, &zz, &tr, &sx, &sy, &inact, &kq, &rq, &lq, kq.len(), 376, nq);
    let fg = family(ln, &[&cert.bc_g], &|_| 0)?;
    let (_, rg, lg) = desc(&fg);
    let kg = vec![10u32; rg.len()];
    pb.gown = aspis_r1_cert_build::fill_own(&al, &zz, &tr, &sx, &sy, &inact, &kg, &rg, &lg, kg.len(), 376, nq);
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
        ru.push(*p.qs.iter().find(|&&u| u / 4 == v)? as u32);
        li.extend(line_inverse(v, 1).iter().map(|&x| wl(x)[0]));
        xs.push(x16(v).0);
    }
    pb.rel = aspis_r1_cert_build::fill_rel(&al, &zz, &tr, &inact, &ti, &opl, &fpos, &rk, &ru, &li, &xs, p.lay.nf, 8 * rk.len());
    pb.round = aspis_r1_cert_build::fill_round(&al, &tr, &inact, &kq, &rq, &lq, kq.len());
    pb.ground = aspis_r1_cert_build::fill_round(&al, &tr, &inact, &kg, &rg, &lg, kg.len());
    let x18s: Vec<u32> = p.lay.fpos.iter().map(|&f| x18(f).0).collect();
    pb.gbat = aspis_r1_cert_build::fill_gbat(&al, &zz, &tr, &inact, &ti, &opl, &x18s, &rg, &lg, rg.len(), p.lay.nf);
    Some(())
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
    extracted_builders(&p, &cert, &ln, &mut pb)?;
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
            if !QUIET.with(|q| q.get()) && !ck::native_workers::is_worker() {
                previous(info)
            }
        }));
    });
}

/// P_chk on one attempt's challenges.  Returns the verdict and the timings.
pub fn p_r1_check(ch: &R1PublicChallenges) -> (bool, R1CheckTimes) {
    let mut tm = R1CheckTimes::default();
    install_quiet_hook();
    QUIET.with(|q| q.set(true));
    let verdict = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> Option<bool> {
        let t = Instant::now();
        let p = public_data(ch)?;
        tm.public_data = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let (cert, _) = emit(&p);
        tm.emit = t.elapsed().as_secs_f64();
        let cert = cert?;
        let t = Instant::now();
        let ln = Lanes::new(&p.cx);
        let (mut pb, cc) = convert(&p, &cert, &ln)?;
        extracted_builders(&p, &cert, &ln, &mut pb)?;
        tm.builders = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let ok = ck::check(&pb, &cc);
        tm.check = t.elapsed().as_secs_f64();
        Some(ok)
    }));
    QUIET.with(|q| q.set(false));
    (matches!(verdict, Ok(Some(true))), tm)
}
