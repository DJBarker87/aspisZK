//! pv-rw-d (2026-11-10): differential tests of the rewritten P_R1 check.
//!
//! `crate::probe_orig` is the pinned source tree (orig/*.rs, byte-identical to
//! 4bb3b3f51e16 docs/research/v8-r0-zk-20261009/z4/*.rs), compiled only under
//! cfg(test).  Every case runs the ORIGINAL `p_r1_check`, the shipped shell
//! `crate::p_r1_check` and the pure core `crate::p_r1_core`, and requires the
//! same accepted bit from all three.
use crate::probe_orig::r1p as orig;
use aspis_core::field::{WideExact as W, CM31, M31, P, QM31};
use aspis_core::r0::CodeField;

/// xorshift64* (the probe's `Rng`), seeded per case.
struct T(u64);
impl T {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0 = self.0.wrapping_mul(0x2545f4914f6cdd1d);
        self.0
    }
    fn m(&mut self) -> M31 {
        let bound = u64::MAX - u64::MAX % P as u64;
        loop {
            let v = self.next();
            if v < bound {
                return M31((v % P as u64) as u32);
            }
        }
    }
    fn q(&mut self) -> QM31 {
        QM31 { c0: CM31::new(self.m(), self.m()), c1: CM31::new(self.m(), self.m()) }
    }
    fn w(&mut self) -> W {
        W::new(self.q(), self.q())
    }
    /// A QM31 point on the circle x^2 + y^2 = 1 (the probe's `circle`).
    fn point(&mut self) -> [QM31; 2] {
        loop {
            let t = self.q();
            if let Some(den) = QM31::ONE.add(t.mul(t)).try_inv() {
                return [QM31::ONE.sub(t.mul(t)).mul(den), t.add(t).mul(den)];
            }
        }
    }
    fn queries(&mut self, n: usize) -> Vec<u32> {
        let mut out: Vec<u32> = vec![];
        while out.len() < n {
            let u = (self.next() % (1 << 18)) as u32;
            if !out.contains(&u) {
                out.push(u);
            }
        }
        out
    }
}

#[derive(Clone)]
struct Case {
    alpha: [QM31; 10],
    z: [[QM31; 2]; 2],
    gamma: W,
    kappa: W,
    alpha0: W,
    alpha1: W,
    queries: Vec<u32>,
}
impl Case {
    fn random(seed: u64) -> Self {
        let mut t = T(seed.wrapping_mul(0x9e3779b97f4a7c15) | 1);
        let alpha = core::array::from_fn(|_| t.q());
        let z = [t.point(), t.point()];
        let (gamma, kappa, alpha0, alpha1) = (t.w(), t.w(), t.w(), t.w());
        let queries = t.queries(22);
        Case { alpha, z, gamma, kappa, alpha0, alpha1, queries }
    }
    fn new_ch(&self) -> crate::R1PublicChallenges {
        crate::R1PublicChallenges { alpha: self.alpha, z: self.z, gamma: self.gamma, kappa: self.kappa, alpha0: self.alpha0, alpha1: self.alpha1, queries: self.queries.clone() }
    }
    fn orig_ch(&self) -> orig::R1PublicChallenges {
        orig::R1PublicChallenges { alpha: self.alpha, z: self.z, gamma: self.gamma, kappa: self.kappa, alpha0: self.alpha0, alpha1: self.alpha1, queries: self.queries.clone() }
    }
}

/// Select the D18 transport in both source trees once, before any compared
/// call.  The z5 transport gate (identical in original and rewrite) is a
/// process-wide OnceLock: two FIRST calls racing on two test threads both see
/// "unselected", and the loser's `set_transport` panics, which the check maps
/// to a rejection.  That is a property of the pinned code (kept unchanged), not
/// of the rewrite; the warm-up removes it from the comparison.  The warm-up
/// input fails after the gate (duplicate query), so it only selects.
fn warm() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        let mut c = Case::random(2);
        c.queries[1] = c.queries[0];
        assert!(!orig::p_r1_check(&c.orig_ch()).0);
        assert!(!crate::p_r1_check(&c.new_ch()).0);
    });
}

/// (original, shell, core) verdicts of one case.
fn verdicts(c: &Case) -> (bool, bool, bool) {
    warm();
    let o = orig::p_r1_check(&c.orig_ch()).0;
    let s = crate::p_r1_check(&c.new_ch()).0;
    let k = crate::p_r1_core_verdict(&c.new_ch());
    (o, s, k)
}

fn agree(label: &str, c: &Case) -> bool {
    let (o, s, k) = verdicts(c);
    eprintln!("PV_RW_D_CASE {label} original={o} shell={s} core={k}");
    assert_eq!(o, s, "{label}: shell differs from the original p_r1_check");
    assert_eq!(s, k, "{label}: core differs from the shell");
    o
}

/// Structured inputs, most of them rejecting: every public_data, emit and
/// checker refusal reachable from the challenge shape.
fn structured() -> Vec<(String, Case)> {
    let base = Case::random(1);
    let half = QM31::from_m31(M31(2).inv());
    let mut v: Vec<(String, Case)> = vec![("base".into(), base.clone())];
    let mut push = |name: &str, f: &dyn Fn(&mut Case)| {
        let mut c = base.clone();
        f(&mut c);
        v.push((name.into(), c));
    };
    push("dup-query", &|c| c.queries[5] = c.queries[3]);
    push("query-2^18", &|c| c.queries[0] = 1 << 18);
    push("query-u32max", &|c| c.queries[21] = u32::MAX);
    push("queries-23", &|c| c.queries.push((c.queries[0] + 1) % (1 << 18)));
    push("queries-21", &|c| {
        c.queries.pop();
    });
    push("queries-0", &|c| c.queries.clear());
    push("queries-1", &|c| c.queries.truncate(1));
    push("queries-sibling", &|c| c.queries[1] = c.queries[0] ^ 1);
    push("queries-unsorted-rev", &|c| c.queries.reverse());
    push("alpha9-half", &|c| c.alpha[9] = half);
    push("alpha-all-zero", &|c| c.alpha = [QM31::ZERO; 10]);
    push("alpha-all-one", &|c| c.alpha = [QM31::ONE; 10]);
    push("alpha0-zero", &|c| c.alpha[0] = QM31::ZERO);
    push("alpha-base-field", &|c| {
        for j in 0..10 {
            c.alpha[j] = QM31::from_m31(c.alpha[j].c0.a);
        }
    });
    push("z-equal", &|c| c.z[1] = c.z[0]);
    push("z-zero", &|c| c.z = [[QM31::ZERO; 2]; 2]);
    push("gamma-zero", &|c| c.gamma = W::ZERO);
    push("kappa-zero", &|c| c.kappa = W::ZERO);
    push("kappa-one", &|c| c.kappa = W::ONE);
    push("alpha0-open-zero", &|c| c.alpha0 = W::ZERO);
    push("alpha1-open-zero", &|c| c.alpha1 = W::ZERO);
    push("openings-equal", &|c| {
        c.alpha1 = c.alpha0;
        c.kappa = c.alpha0;
    });
    v
}

#[test]
fn rewritten_check_agrees_with_original_on_structured_inputs() {
    let mut acc = 0;
    let all = structured();
    for (name, c) in &all {
        acc += agree(name, c) as usize;
    }
    eprintln!("PV_RW_D_STRUCTURED cases={} accepted={acc}", all.len());
    assert!(acc < all.len(), "the structured set must contain rejecting inputs");
}

#[test]
fn rewritten_check_agrees_with_original_on_random_inputs() {
    let n: u64 = std::env::var("PV_RW_D_RANDOM").ok().and_then(|s| s.parse().ok()).unwrap_or(24);
    let mut acc = 0;
    for seed in 0..n {
        acc += agree(&format!("random-{seed}"), &Case::random(1000 + seed)) as usize;
    }
    eprintln!("PV_RW_D_RANDOM cases={n} accepted={acc}");
}

/// Wall time of the original and the rewritten check (release build), one
/// accepting case; run with --ignored --nocapture.
#[test]
#[ignore]
fn timing() {
    warm();
    let c = Case::random(7);
    let reps: usize = std::env::var("PV_RW_D_REPS").ok().and_then(|s| s.parse().ok()).unwrap_or(3);
    for _ in 0..reps {
        let t = std::time::Instant::now();
        let (o, tm) = orig::p_r1_check(&c.orig_ch());
        let to = t.elapsed().as_secs_f64();
        let t = std::time::Instant::now();
        let (s, tn) = crate::p_r1_check(&c.new_ch());
        let ts = t.elapsed().as_secs_f64();
        let t = std::time::Instant::now();
        let k = crate::p_r1_core_verdict(&c.new_ch());
        let tk = t.elapsed().as_secs_f64();
        eprintln!("PV_RW_D_TIMING original={to:.3}s ({o}; {tm:?}) shell={ts:.3}s ({s}; {tn:?}) core={tk:.3}s ({k})");
    }
}
