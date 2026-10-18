//! Z9 (LOG cross-reference 2026-10-13 "the R1 programme in the Rust PLAN"):
//! the Z8c silent-rank gate and the D23 decomposition on the R1 payload
//! (variant S2 of crates/aspis-r1-cost-probe at origin/codex/100bit-spend-path-
//! 20261013 1822c2ced): D18 transport, two folds, 64 final values, gamma in
//! WideExact (the checkpoint's two fixed limb sets), kappa/alpha0/alpha1 uniform
//! in WideExact, rho in QM31 (it enters no disclosed coordinate). Real R1
//! coordinates, no proxy, balanced (Lean `balance 0`) mask space.
//! Exact M31/QM31/WideExact arithmetic. Not a Lean proof.
//!
//! Provenance. `trial`, `alpha_for`, `lambda_dims`, `round_polys`, `Proj`,
//! `lane_stage`, `lane_kernel`, `lane_elim`, `Lanes`, `conditioned_sources`
//! and the (i')/(ii') block are copied from z8c.rs (constant batch widths made
//! runtime). The R1 functions in `mod r1` are copied from the spend-path
//! source (weights.rs Weights::new/raw/tensor/pair/materialize,
//! grouped_inactive_pair, twofold_libra_weights; prover.rs round/fold;
//! host_commitment.rs EncodingDomain::new/evaluate; verifier.rs circle_fold,
//! line_fold, accumulate's basis; transport.rs Variant::S2 row) with
//! fast_pairing::EbyKDot replaced by a plain E-by-K sum and fast_domain by
//! aspis_core::r0::domain (the spend-path tests assert those equivalences).
#![allow(dead_code)]
use super::*;
use aspis_core::field::WideExact as W;
use aspis_core::r0::domain::{fibre_point, FibreIndex as FI};

const MASTER: u64 = 0x5348f0b9a87835d0;
const STRUCT_SEED: u64 = 0x5a38_d20b_2026_1013;
const OPEN_SEED9: u64 = 0x5a39_0be0_2026_1017;
// Order kept from z8c so that A, B, I, J (and K, L, M) keep their alpha seeds.
const STRUCTURES: [&str; 7] = ["A", "B", "I", "J", "K", "L", "M"];
const RW: usize = 1084; // round coordinates (Z4c layout)
#[path = "z9b.rs"]
pub(super) mod z9b;
const THREADS: usize = 4;

// ---------------------------------------------------------------- R1 ports
mod r1 {
    use super::W as E;
    use aspis_core::field::{M31, QM31 as K};
    pub const QUARTER: M31 = M31(536870912);
    pub const PERM: [usize; 4] = [0, 3, 2, 1];
    pub const TAU: [usize; 5] = [3, 4, 2, 0, 1];
    /// transport.rs Variant::S2 `row`: coefficient j sits at row(j).
    pub fn row(j: usize) -> usize {
        let mut out = 0;
        for d in 0..5 {
            out |= ((j >> (2 * d)) & 3) << (2 * TAU[d]);
        }
        out
    }
    pub fn coefficients<T: Copy>(rows: &[T; 1024]) -> [T; 1024] {
        core::array::from_fn(|j| rows[row(j)])
    }
    pub fn powers<const N: usize>(x: E) -> [E; N] {
        let mut p = E::ONE;
        core::array::from_fn(|_| {
            let a = p;
            p = p.mul(x);
            a
        })
    }
    pub fn kpowers<const N: usize>(x: K) -> [K; N] {
        let mut p = K::ONE;
        core::array::from_fn(|_| {
            let a = p;
            p = p.mul(x);
            a
        })
    }
    pub fn double(x: K) -> K {
        x.mul(x).add(x.mul(x)).sub(K::ONE)
    }
    fn dot(a: &[E], k: &[K]) -> E {
        a.iter().zip(k).fold(E::ZERO, |s, (x, y)| s.add(x.mul_qm31(*y)))
    }
    pub struct Weights {
        pub factors: [[[K; 4]; 5]; 5],
        pub points: [[K; 10]; 3],
        pub extra: [K; 2],
    }
    impl Weights {
        pub fn new(alpha: &[K; 10], z: &[[K; 2]; 2]) -> Self {
            let points = aspis_core::state_only_prefix::r0::statement_points(alpha);
            let mut factors = [[[K::ZERO; 4]; 5]; 5];
            for k in 0..3 {
                for d in 0..5 {
                    let a = points[k][9 - 2 * TAU[d]];
                    let b = points[k][8 - 2 * TAU[d]];
                    factors[k][d] = [K::ONE.sub(a).mul(K::ONE.sub(b)), a.mul(K::ONE.sub(b)), K::ONE.sub(a).mul(b), a.mul(b)];
                }
            }
            for k in 0..2 {
                let (zx, zy) = (z[k][0], z[k][1]);
                factors[3 + k][0] = [K::ONE, zy, zx, zx.mul(zy)];
                let mut x = double(zx);
                for d in 1..5 {
                    let y = double(x);
                    factors[3 + k][d] = [K::ONE, x, y, x.mul(y)];
                    x = double(y);
                }
            }
            Self { factors, points, extra: [alpha[8], alpha[9]] }
        }
        pub fn raw(&self, kind: usize, j: usize, inactive: impl Fn(usize) -> bool) -> K {
            match kind {
                0 => if inactive(row(j)) { K::ONE } else { K::ZERO },
                4 => if j < 56 { self.extra[j / 28].pow((j % 28) as u64) } else { K::ZERO },
                _ => {
                    let k = if kind < 4 { kind - 1 } else { kind - 2 };
                    (0..5).fold(K::ONE, |v, d| v.mul(self.factors[k][d][(j >> (2 * d)) & 3]))
                }
            }
        }
        fn scalar_factor(f: &[K; 4], p: &[E; 4]) -> E {
            (0..4).fold(E::ZERO, |v, s| v.add(p[PERM[s]].mul_qm31(f[s]))).mul_m31(QUARTER)
        }
        fn tensor(&self, k: usize, folds: usize, output: &mut [K]) {
            output[0] = K::ONE;
            let mut n = 1;
            for d in folds..5 {
                for j in (0..n).rev() {
                    let x = output[j];
                    for s in 0..4 {
                        output[j + s * n] = x.mul(self.factors[k][d][s]);
                    }
                }
                n *= 4;
            }
        }
        /// weights.rs `pair` on the S2 two-fold path (f = 64 final values).
        pub fn pair(&self, alpha: &[E; 2], f: &[E], kappa: E, inactive: impl Fn(usize) -> bool + Copy) -> E {
            let n = f.len();
            assert_eq!(n, 64);
            let folds = 2;
            let ap0 = powers::<4>(alpha[0]);
            let ap1 = powers::<4>(alpha[1]);
            let mut scratch = vec![K::ZERO; n];
            let mut parts = [E::ZERO; 7];
            let shared_two_point = self.factors[0][2] == self.factors[2][2] && self.factors[0][3] == self.factors[2][3];
            for kind in [1usize, 2, 3, 5, 6] {
                if shared_two_point && (kind == 1 || kind == 3) {
                    continue;
                }
                let k = if kind < 4 { kind - 1 } else { kind - 2 };
                self.tensor(k, folds, &mut scratch);
                let scale = Self::scalar_factor(&self.factors[k][0], &ap0).mul(Self::scalar_factor(&self.factors[k][1], &ap1));
                parts[kind] = scale.mul(dot(f, &scratch));
            }
            if shared_two_point {
                let common: [K; 16] = core::array::from_fn(|j| self.factors[0][2][j & 3].mul(self.factors[0][3][j >> 2]));
                let partials: [E; 4] = core::array::from_fn(|s| dot(&f[16 * s..16 * s + 16], &common));
                for (kind, k) in [(1usize, 0usize), (3usize, 2usize)] {
                    let high = dot(&partials, &self.factors[k][4]);
                    let scale = Self::scalar_factor(&self.factors[k][0], &ap0).mul(Self::scalar_factor(&self.factors[k][1], &ap1));
                    parts[kind] = scale.mul(high);
                }
            }
            let low: [E; 16] = core::array::from_fn(|s| ap0[PERM[s % 4]].mul(ap1[PERM[s / 4]]).mul_m31(QUARTER.mul(QUARTER)));
            // grouped_inactive_pair
            {
                let mut group_masks = [0u16; 64];
                let mut group_coefficients = [E::ZERO; 64];
                let mut groups = 0;
                for j in 0..n {
                    let mut mask = 0u16;
                    for s in 0..16 {
                        if self.raw(0, 16 * j + s, inactive) == K::ONE {
                            mask |= 1 << s;
                        }
                    }
                    let mut group = 0;
                    while group < groups && group_masks[group] != mask {
                        group += 1;
                    }
                    if group == groups {
                        group_masks[group] = mask;
                        groups += 1;
                    }
                    group_coefficients[group] = group_coefficients[group].add(f[j]);
                }
                for group in 0..groups {
                    let mask = group_masks[group];
                    let mut weight = E::ZERO;
                    for (s, &c) in low.iter().enumerate() {
                        if mask & (1 << s) != 0 {
                            weight = weight.add(c);
                        }
                    }
                    parts[0] = parts[0].add(group_coefficients[group].mul(weight));
                }
            }
            // twofold_libra_weights
            {
                let pw: [[K; 28]; 2] = core::array::from_fn(|side| kpowers::<28>(self.extra[side]));
                let libra: [E; 4] = core::array::from_fn(|j| {
                    let mut weight = E::ZERO;
                    for s in 0..16 {
                        let index = 16 * j + s;
                        if index < 56 {
                            weight = weight.add(low[s].mul_qm31(pw[index / 28][index % 28]));
                        }
                    }
                    weight
                });
                for j in 0..4 {
                    parts[4] = parts[4].add(f[j].mul(libra[j]));
                }
            }
            let k = powers::<7>(kappa);
            (0..7).fold(E::ZERO, |s, kind| s.add(k[kind].mul(parts[kind])))
        }
        pub fn materialize(&self, kappa: E, inactive: impl Fn(usize) -> bool + Copy) -> Vec<E> {
            let kp = powers::<7>(kappa);
            (0..1024)
                .map(|j| (0..7).fold(E::ZERO, |v, kind| v.add(kp[kind].mul_qm31(self.raw(kind, j, inactive)))))
                .collect()
        }
    }
    /// prover.rs `round`.
    pub fn round(q: &[E], w: &[E]) -> [E; 7] {
        assert_eq!(q.len(), w.len());
        let mut c = [E::ZERO; 7];
        for d in 0..q.len() / 4 {
            for s in 0..4 {
                for t in 0..4 {
                    c[s + PERM[t]] = c[s + PERM[t]].add(q[4 * d + s].mul(w[4 * d + t]));
                }
            }
        }
        c.map(|x| x.mul_m31(QUARTER))
    }
    /// prover.rs `fold`.
    pub fn fold(q: &[E], alpha: E, dual: bool) -> Vec<E> {
        q.chunks_exact(4)
            .map(|h| {
                if dual {
                    h[0].add(alpha.mul(h[3].add(alpha.mul(h[2].add(alpha.mul(h[1])))))).mul_m31(QUARTER)
                } else {
                    h[0].add(alpha.mul(h[1].add(alpha.mul(h[2].add(alpha.mul(h[3]))))))
                }
            })
            .collect()
    }
    pub fn poly(c: &[E], x: E) -> E {
        c.iter().rev().fold(E::ZERO, |a, v| a.mul(x).add(*v))
    }
}

// ------------------------------------------------- R1 geometry (verifier/host)
/// host_commitment.rs EncodingDomain: levels[0][u] = 2 x_u^2 - 1 over the 2^18
/// fibre points, levels[d+1][j] = 2 levels[d][2j]^2 - 1.
struct Geo {
    levels: Vec<Vec<M31>>,
}
impl Geo {
    fn new() -> Self {
        let n = aspis_core::r0::FIBRE_COUNT;
        let first: Vec<M31> = (0..n)
            .map(|u| {
                let z = fibre_point::<M31>(FI::new(u).unwrap());
                z.x.mul(z.x).double().sub(M31::ONE)
            })
            .collect();
        let mut levels = vec![first];
        for depth in 0..8 {
            let next: Vec<M31> = (0..levels[depth].len() / 2)
                .map(|j| levels[depth][2 * j].mul(levels[depth][2 * j]).double().sub(M31::ONE))
                .collect();
            levels.push(next);
        }
        Geo { levels }
    }
    /// host_commitment.rs EncodingDomain::evaluate (verbatim recursion).
    fn evaluate(&self, coefficients: &[W], depth: usize) -> Vec<W> {
        let nodes = &self.levels[depth];
        if coefficients.len() == 1 {
            return vec![coefficients[0]; nodes.len()];
        }
        let even: Vec<W> = (0..coefficients.len() / 2).map(|j| coefficients[2 * j]).collect();
        let odd: Vec<W> = (0..coefficients.len() / 2).map(|j| coefficients[2 * j + 1]).collect();
        let a = self.evaluate(&even, depth + 1);
        let b = self.evaluate(&odd, depth + 1);
        (0..nodes.len()).map(|j| a[j / 2].add(W::from_m31(nodes[j]).mul(b[j / 2]))).collect()
    }
    /// Closed form of `evaluate(q1, 0)[i]` for the unit q1 = e_d (256 coefficients):
    /// prod over set bits b of d of levels[b][i >> b].
    fn unit_eval(&self, d: usize, i: usize) -> M31 {
        (0..8).filter(|b| d >> b & 1 == 1).fold(M31::ONE, |v, b| v.mul(self.levels[b][i >> b]))
    }
}
fn line_node(u: usize) -> M31 {
    let x = fibre_point::<M31>(FI::new(u).unwrap()).x;
    x.mul(x).double().sub(M31::ONE)
}
/// verifier.rs circle_fold.
fn circle_fold(alpha: W, u: usize, a: [W; 4]) -> W {
    let p = fibre_point::<M31>(FI::new(u).unwrap());
    let q = r1::QUARTER;
    let ix = p.x.inv();
    let iy = p.y.inv();
    let [a, b, c, d] = a;
    let h0 = a.add(b).add(c).add(d).mul_m31(q);
    let h1 = a.sub(b).sub(c).add(d).mul_m31(q.mul(iy));
    let h2 = a.add(b).sub(c).sub(d).mul_m31(q.mul(ix));
    let h3 = a.sub(b).add(c).sub(d).mul_m31(q.mul(ix).mul(iy));
    h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
}
/// verifier.rs line_fold (v = u / 4).
fn line_fold(alpha: W, v: usize, a: [W; 4]) -> W {
    let x = line_node(4 * v);
    let y = line_node(4 * v + 3);
    let z = x.mul(x).double().sub(M31::ONE);
    let half = M31(1073741824);
    let q = r1::QUARTER;
    let [a, b, c, d] = a;
    let h0 = a.add(b).add(c).add(d).mul_m31(q);
    let h2 = a.add(b).sub(c).sub(d).mul_m31(q.mul(z.inv()));
    let c0 = a.sub(b).mul_m31(half.mul(x.inv()));
    let c1 = d.sub(c).mul_m31(half.mul(y.inv()));
    let h1 = c0.add(c1).mul_m31(half);
    let h3 = c0.sub(c1).mul_m31(half.mul(z.inv()));
    h0.add(alpha.mul(h1.add(alpha.mul(h2.add(alpha.mul(h3))))))
}
/// verifier.rs accumulate: the 64 final-message basis values for query u (folds = 2).
fn final_basis(u: usize) -> [M31; 64] {
    let mut node = line_node(u / 4 * 4);
    for _ in 0..2 {
        node = node.mul(node).double().sub(M31::ONE);
    }
    let mut basis = [M31::ZERO; 64];
    basis[0] = M31::ONE;
    let mut n = 1;
    while n < 64 {
        for j in 0..n {
            basis[n + j] = basis[j].mul(node);
        }
        node = node.mul(node).double().sub(M31::ONE);
        n *= 2;
    }
    basis
}

// ------------------------------------------------------------- trial (z8c)
struct Trial {
    a: [QM31; 10],
    z: [Point<QM31>; 2],
    qs: Vec<usize>,
    ch: Challenges,
    tapes: Vec<Trace>,
}
/// Exact replay of z4c_main's RNG consumption (copied from z8c.rs).
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
    v.chunks(4).map(|c| QM31 { c0: CM31::new(c[0], c[1]), c1: CM31::new(c[2], c[3]) }).collect()
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
fn in_k2(x: QM31) -> bool {
    x.c1 == CM31::new(M31::ZERO, M31::ZERO)
}
fn good3(a: &[QM31; 10]) -> bool {
    (0..4).filter(|&i| !in_k2(a[i])).count() >= 3
}
/// z8c.rs alpha_for (same seeds).
fn alpha_for(s: &str, v: usize, base: &[QM31; 10]) -> [QM31; 10] {
    let si = STRUCTURES.iter().position(|x| *x == s).unwrap() as u64;
    let mut rng = Rng(STRUCT_SEED.wrapping_add((si * 64 + v as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15)));
    let mut a = *base;
    match s {
        "A" => {}
        "B" => (0..10).for_each(|i| a[i] = f_nontrivial(&mut rng, i == 9)),
        "I" => (0..10).for_each(|i| a[i] = k2_nontrivial(&mut rng, i == 9)),
        "J" => (1..7).for_each(|i| a[i] = f_nontrivial(&mut rng, false)),
        "K" => (2..4).for_each(|i| a[i] = f_nontrivial(&mut rng, false)),
        "L" => {
            (0..6).for_each(|i| a[i] = f_nontrivial(&mut rng, false));
            assert!(!in_k2(a[6]), "structure L needs alpha_6 outside K2");
        }
        "M" => (3..7).for_each(|i| a[i] = f_nontrivial(&mut rng, false)),
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
                let x = (0..j).fold(QM31::ONE, |v, i| v.mul(if l >> i & 1 == 1 { a[i] } else { QM31::ONE.sub(a[i]) }));
                e.insert(limbs(x).to_vec());
            }
            e.rank
        })
        .collect()
}
fn round_polys(v: &[QM31], a: &[QM31; 10]) -> Vec<[QM31; 28]> {
    let mut prev = v[0];
    let mut out = vec![];
    for j in 0..10 {
        let mut co = [QM31::ZERO; 28];
        co[0] = v[1 + 27 * j];
        co[2..].copy_from_slice(&v[2 + 27 * j..28 + 27 * j]);
        co[1] = prev.sub(co[0].add(co[0])).sub(co[2..].iter().fold(QM31::ZERO, |v, x| v.add(*x)));
        prev = co.iter().rev().fold(QM31::ZERO, |v, x| v.mul(a[j]).add(*x));
        out.push(co);
    }
    out
}
struct Proj {
    full: Vec<Ech<M31>>,
    limb: Vec<Vec<Ech<M31>>>,
}
impl Proj {
    fn of(e: &Ech<M31>, a: &[QM31; 10]) -> Self {
        let mut p = Proj { full: (0..10).map(|_| Ech::new(112)).collect(), limb: (0..10).map(|_| (0..4).map(|_| Ech::new(28)).collect()).collect() };
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
fn w_uniform(rng: &mut Rng) -> W {
    W::new(rng.q(), rng.q())
}
fn wflat(v: &[W]) -> Vec<M31> {
    v.iter().flat_map(|x| wlimbs(*x)).collect()
}
fn wvals(limbs: &[M31]) -> Vec<W> {
    limbs.chunks(8).map(|c| W::from_limbs(std::array::from_fn(|i| c[i].0)).unwrap()).collect()
}
fn wunit(m: usize) -> W {
    let mut l = [0u32; 8];
    l[m] = 1;
    W::from_limbs(l).unwrap()
}
fn sub_vec<T: Copy>(a: &[T], b: &[T], f: impl Fn(T, T) -> T) -> Vec<T> {
    a.iter().zip(b).map(|(x, y)| f(*x, *y)).collect()
}
fn scale(v: &[QM31], x: QM31) -> Vec<QM31> {
    v.iter().map(|y| y.mul(x)).collect()
}
fn sigma(x: W) -> W {
    W::new(x.c0(), QM31::ZERO.sub(x.c1()))
}

// ------------------------------------------------------ opening challenges
/// The spend-path checkpoint's two fixed gamma limb sets (privacy-wide/probe.rs gamma_limbs/test_gamma).
fn gamma_limbs(index: usize) -> [u32; 8] {
    match index {
        0 => [7, 11, 13, 17, 19, 23, 29, 31],
        1 => [37, 41, 43, 47, 53, 59, 61, 67],
        _ => panic!("gamma index must be 0 or 1"),
    }
}
fn test_gamma(index: usize) -> W {
    let limbs = gamma_limbs(index);
    let k = |i: usize| M31(limbs[i]);
    W::new(QM31 { c0: CM31::new(k(0), k(1)), c1: CM31::new(k(2), k(3)) }, QM31 { c0: CM31::new(k(4), k(5)), c1: CM31::new(k(6), k(7)) })
}
struct Opening {
    gamma: W,
    kappa: W,
    alpha0: W,
    alpha1: W,
}
/// kappa (row 28), alpha0 (29), alpha1 (30) uniform in WideExact, one stream per
/// vector shared by every structure and both gammas.
fn opening_challenges(v: usize, gi: usize) -> Opening {
    let mut rng = Rng(OPEN_SEED9.wrapping_add((v as u64 + 1).wrapping_mul(0x9e3779b97f4a7c15)));
    Opening { gamma: test_gamma(gi), kappa: w_uniform(&mut rng), alpha0: w_uniform(&mut rng), alpha1: w_uniform(&mut rng) }
}
/// D18 row -> coefficient (privacy-wide/probe.rs d18_transport), checked against r1::row.
fn d18_transport() -> [u16; N] {
    std::array::from_fn(|r| {
        let digit = |d: usize| (r >> (2 * d)) & 3;
        (digit(3) + 4 * digit(4) + 16 * digit(2) + 64 * digit(0) + 256 * digit(1)) as u16
    })
}

// ------------------------------------------------------- batched layout
/// Batched coordinates (E values): 0 inactive; 1..=7 round0 h0..h6; 8..=14
/// round1 g0..g6; 15..15+nf folded-word values at `fpos`; then final f0..f63.
struct Lay {
    fpos: Vec<usize>,
    nf: usize,
    nb: usize,
    bw: usize,
    tw: usize,
}
impl Lay {
    fn new(qs: &[usize]) -> Self {
        let mut fpos: Vec<usize> = qs.iter().flat_map(|&u| (0..4).map(move |s| 4 * (u / 4) + s)).collect();
        fpos.sort();
        fpos.dedup();
        let nf = fpos.len();
        let nb = 15 + nf + 64;
        Lay { fpos, nf, nb, bw: 8 * nb, tw: 8 * nb + RW }
    }
    fn fw(&self, pos: usize) -> usize {
        15 + self.fpos.binary_search(&pos).expect("folded position")
    }
    fn fin(&self, e: usize) -> usize {
        15 + self.nf + e
    }
    fn label(&self, i: usize) -> String {
        match i {
            0 => "ia".into(),
            1..=7 => format!("h{}", i - 1),
            8..=14 => format!("g{}", i - 8),
            _ if i < 15 + self.nf => format!("w{}", self.fpos[i - 15]),
            _ => format!("f{}", i - 15 - self.nf),
        }
    }
}
struct Ctx {
    a: [QM31; 10],
    br: Vec<Vec<M31>>,
    gr: Vec<Vec<QM31>>,
    tail: Vec<Vec<QM31>>,
    beta: Vec<Vec<W>>, // row-indexed, length nb
    gpow: Vec<W>,
    lay: Lay,
}
impl Ctx {
    fn batched(&self, lane: usize, x: W, r: usize) -> Vec<W> {
        let g = self.gpow[lane].mul(x);
        self.beta[r].iter().map(|b| g.mul(*b)).collect()
    }
}
fn inactive_fn(r: usize) -> bool {
    inactive(r)
}
/// phi[k] = batched payload of the unit natural coefficient e_k (gamma^lane omitted):
/// [inactive, round(e_k, w), round(fold(e_k), w1), folded word at fpos, fold(fold(e_k))].
fn unit_functionals(geo: &Geo, w: &[W], op: &Opening, lay: &Lay) -> Vec<Vec<W>> {
    let w1 = r1::fold(w, op.alpha0, true);
    let ks: Vec<usize> = (0..1024).collect();
    let chunk = ks.len().div_ceil(THREADS);
    std::thread::scope(|s| {
        let hs: Vec<_> = ks
            .chunks(chunk)
            .map(|part| {
                let w1 = &w1;
                s.spawn(move || {
                    part.iter()
                        .map(|&k| {
                            let mut e = vec![W::ZERO; 1024];
                            e[k] = W::ONE;
                            let mut out = vec![W::ZERO; lay.nb];
                            out[0] = if inactive(r1::row(k)) { W::ONE } else { W::ZERO };
                            out[1..8].copy_from_slice(&r1::round(&e, w));
                            let q1 = r1::fold(&e, op.alpha0, false);
                            out[8..15].copy_from_slice(&r1::round(&q1, w1));
                            for (n, &i) in lay.fpos.iter().enumerate() {
                                out[15 + n] = (0..256).filter(|&d| q1[d] != W::ZERO).fold(W::ZERO, |acc, d| acc.add(q1[d].mul_m31(geo.unit_eval(d, i))));
                            }
                            let f = r1::fold(&q1, op.alpha1, false);
                            for e2 in 0..64 {
                                out[lay.fin(e2)] = f[e2];
                            }
                            out
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        hs.into_iter().flat_map(|h| h.join().unwrap()).collect()
    })
}

/// Whole-column R1 pipeline (prover.rs prove_from_semantics, from q on) on
/// random words of lanes 16 (F), 26, 27, 28 (K4) equals the sum of per-row
/// batched vectors; and on the same (not own-silent) words every verifier
/// equation of verifier.rs holds: S2a with the full kappa-claim, S2b, S1 by
/// Weights::pair and by the double dual fold, C_u (circle_fold of the batched
/// opened symbols equals the folded word), L_u (line_fold equals the final
/// message at the query's basis). Also checks the folded closed form.
fn pipeline_check(cx: &Ctx, geo: &Geo, wts: &r1::Weights, w: &[W], op: &Opening, qs: &[usize], seed: u64) {
    let lay = &cx.lay;
    let mut rng = Rng(seed);
    let mut q = vec![W::ZERO; 1024];
    let mut expected = vec![W::ZERO; lay.nb];
    let k7 = r1::powers::<7>(op.kappa);
    let mut parts = [W::ZERO; 7];
    let mut dots = vec![[W::ZERO; 4]; qs.len()];
    for lane in [16usize, 26, 27, 28] {
        let rows: [QM31; 1024] = std::array::from_fn(|_| if lane < 26 { QM31::from_m31(rng.m()) } else { rng.q() });
        let co = r1::coefficients(&rows);
        let g = cx.gpow[lane];
        for j in 0..1024 {
            q[j] = q[j].add(g.mul(wq(co[j])));
        }
        let own: Vec<QM31> = (0..95).map(|i| (0..N).fold(QM31::ZERO, |s, r| s.add(rows[r].mul(cx.gr[r][i])))).collect();
        for p in 0..6 {
            parts[1 + p] = parts[1 + p].add(g.mul(wq(own[1 + p])));
        }
        for qi in 0..qs.len() {
            for s in 0..4 {
                dots[qi][s] = dots[qi][s].add(g.mul(wq(own[7 + 4 * qi + s])));
            }
        }
        for r in 0..N {
            for (e, b) in expected.iter_mut().zip(cx.batched(lane, wq(rows[r]), r)) {
                *e = e.add(b);
            }
        }
    }
    let inact = (0..1024).fold(W::ZERO, |s, j| s.add(q[j].mul_qm31(wts.raw(0, j, inactive_fn))));
    parts[0] = inact;
    let claim = (0..7).fold(W::ZERO, |s, i| s.add(k7[i].mul(parts[i])));
    let qw = (0..1024).fold(W::ZERO, |s, j| s.add(q[j].mul(w[j])));
    assert_eq!(claim, qw, "kappa claim equals <q, w>");
    let c0 = r1::round(&q, w);
    let q1 = r1::fold(&q, op.alpha0, false);
    let w1 = r1::fold(w, op.alpha0, true);
    let fword = geo.evaluate(&q1, 0);
    assert_eq!(fword.len(), aspis_core::r0::FIBRE_COUNT);
    let c1 = r1::round(&q1, &w1);
    let fin = r1::fold(&q1, op.alpha1, false);
    let w2 = r1::fold(&w1, op.alpha1, true);
    let mut direct = vec![inact];
    direct.extend_from_slice(&c0);
    direct.extend_from_slice(&c1);
    for &i in &lay.fpos {
        direct.push(fword[i]);
    }
    direct.extend_from_slice(&fin);
    assert_eq!(direct, expected, "column-wise decomposition");
    let quarter = W::from_m31(r1::QUARTER);
    assert_eq!(c0[0].add(c0[4]), claim.mul(quarter), "S2a (round0 boundary) on a full view");
    assert_eq!(c1[0].add(c1[4]), r1::poly(&c0, op.alpha0).mul(quarter), "S2b");
    let pair = wts.pair(&[op.alpha0, op.alpha1], &fin, op.kappa, inactive_fn);
    let pw2 = (0..64).fold(W::ZERO, |s, e| s.add(fin[e].mul(w2[e])));
    assert_eq!(pair, r1::poly(&c1, op.alpha1), "S1 via Weights::pair");
    assert_eq!(pw2, pair, "S1 via double dual fold");
    for (qi, &u) in qs.iter().enumerate() {
        assert_eq!(circle_fold(op.alpha0, u, dots[qi]), fword[u], "C_u u={u}");
        let v = u / 4;
        let vals = [fword[4 * v], fword[4 * v + 1], fword[4 * v + 2], fword[4 * v + 3]];
        let basis = final_basis(u);
        let rhs = (0..64).fold(W::ZERO, |s, e| s.add(fin[e].mul_m31(basis[e])));
        assert_eq!(line_fold(op.alpha1, v, vals), rhs, "L_u u={u}");
    }
    println!(
        "Z9_CHECK pipeline lanes=[16,26,27,28] whole_column_equals_rowwise_sum=true coordinates={} verifier_equations=S2a,S2b,S1(pair),S1(w2),C_u(22),L_u(22) hold=true",
        lay.nb
    );
}

/// A K-linear relation on the batched coordinates.
struct Rel {
    name: String,
    c: Vec<(usize, W)>,
}
impl Rel {
    fn eval(&self, y: &[W]) -> W {
        self.c.iter().fold(W::ZERO, |s, (i, c)| s.add(c.mul(y[*i])))
    }
    fn limb_functionals(&self, bw: usize) -> Vec<Vec<M31>> {
        (0..8)
            .map(|k| {
                let mut v = vec![M31::ZERO; bw];
                for (i, c) in &self.c {
                    for m in 0..8 {
                        v[8 * i + m] = v[8 * i + m].add(M31(c.mul(wunit(m)).to_limbs()[k]));
                    }
                }
                v
            })
            .collect()
    }
}
/// The R1 verifier relations on own-silent tapes (verifier.rs finish_relation,
/// query_with_geometry, accumulate; own observations zero).
struct Relations {
    ia: Rel,
    s2a: Rel,
    s2b: Rel,
    s1: Rel,
    cu: Vec<Rel>,
    lu: Vec<Rel>,
    low: Vec<Rel>, // f0..f3 (D-high candidates)
}
fn relations(w: &[W], op: &Opening, qs: &[usize], lay: &Lay) -> Relations {
    let quarter = W::from_m31(r1::QUARTER);
    let w1 = r1::fold(w, op.alpha0, true);
    let w2 = r1::fold(&w1, op.alpha1, true);
    let neg = |x: W| W::ZERO.sub(x);
    let mut s2b = vec![(8, W::ONE), (12, W::ONE)];
    let mut p = W::ONE;
    for i in 0..7 {
        s2b.push((1 + i, neg(quarter.mul(p))));
        p = p.mul(op.alpha0);
    }
    let mut s1 = vec![];
    let mut p = W::ONE;
    for i in 0..7 {
        s1.push((8 + i, p));
        p = p.mul(op.alpha1);
    }
    for e in 0..64 {
        s1.push((lay.fin(e), neg(w2[e])));
    }
    let cu = qs.iter().map(|&u| Rel { name: format!("C_u{u}"), c: vec![(lay.fw(u), W::ONE)] }).collect();
    let lu = qs
        .iter()
        .map(|&u| {
            let v = u / 4;
            let mut c = vec![];
            for t in 0..4 {
                let mut unit = [W::ZERO; 4];
                unit[t] = W::ONE;
                c.push((lay.fw(4 * v + t), line_fold(op.alpha1, v, unit)));
            }
            let basis = final_basis(u);
            for e in 0..64 {
                c.push((lay.fin(e), neg(W::from_m31(basis[e]))));
            }
            Rel { name: format!("L_u{u}"), c }
        })
        .collect();
    Relations {
        ia: Rel { name: "ia".into(), c: vec![(0, W::ONE)] },
        s2a: Rel { name: "S2a".into(), c: vec![(1, W::ONE), (5, W::ONE)] },
        s2b: Rel { name: "S2b".into(), c: s2b },
        s1: Rel { name: "S1".into(), c: s1 },
        cu,
        lu,
        low: (0..4).map(|e| Rel { name: format!("f{e}"), c: vec![(lay.fin(e), W::ONE)] }).collect(),
    }
}

// ------------------------------------------------- elimination (from z8c)
/// z8c `lane_stage` (carry width taken from the source).
fn lane_stage(count: usize, mut source: impl FnMut(usize) -> (Vec<M31>, Vec<M31>), targets: &[Vec<M31>], tw: usize, global: &mut Ech<M31>) -> Vec<Vec<M31>> {
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
            None => {
                global.insert(c);
            }
        }
    }
    targets
        .iter()
        .map(|t| {
            let mut v = t.clone();
            let mut out = vec![M31::ZERO; tw];
            for i in 0..v.len() {
                if v[i] == M31::ZERO {
                    continue;
                }
                let (b, bc) = piv[i].as_ref().expect("per-lane target outside lane coordinate span");
                let s = v[i];
                for j in i..v.len() {
                    v[j] = v[j].sub(s.mul(b[j]));
                }
                for j in 0..tw {
                    out[j] = out[j].add(s.mul(bc[j]));
                }
            }
            out
        })
        .collect()
}
/// z8c `lane_elim`: kernel carries to `sink`, returns the pivot rows.
fn lane_elim(count: usize, mut source: impl FnMut(usize) -> (Vec<M31>, Vec<M31>), mut sink: impl FnMut(Vec<M31>)) -> Vec<Vec<M31>> {
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
    piv.into_iter().flatten().map(|(v, _)| v).collect()
}
fn carry(batched: &[W], round: &[QM31]) -> Vec<M31> {
    let mut c = wflat(batched);
    c.extend(flatten(round));
    c
}
fn ech_rows(e: &Ech<M31>) -> Vec<Vec<M31>> {
    e.p.iter().flatten().cloned().collect()
}
fn rank_of(width: usize, vs: impl Iterator<Item = Vec<M31>>) -> usize {
    let mut e = Ech::new(width);
    for v in vs {
        e.insert(v);
    }
    e.rank
}
fn slice_image(e: &Ech<M31>, from: usize, bw: usize) -> Ech<M31> {
    let mut out = Ech::new(RW);
    for (i, row) in e.p.iter().enumerate() {
        if let Some(v) = row {
            if i >= from {
                out.insert(v[bw..].to_vec());
            }
        }
    }
    out
}
fn batched_reduce(e: &Ech<M31>, mut v: Vec<M31>, bw: usize) -> Vec<M31> {
    for i in 0..bw {
        if v[i] == M31::ZERO {
            continue;
        }
        if let Some(b) = &e.p[i] {
            let s = v[i];
            for j in i..v.len() {
                v[j] = v[j].sub(s.mul(b[j]));
            }
        }
    }
    v
}
fn report(label: &str, kind: &str, total: usize, p: &Proj) {
    println!("Z9_RANKS {label} kind={kind} total={total} round_full={:?} round_limb={:?}", p.full_ranks(), p.limb_ranks());
}

const LANES: usize = 12; // mask-only 0..9 (phys 16..25), G (27), D (28)
const DW: usize = 376;
fn lane_name(li: usize) -> String {
    match li {
        0..=9 => format!("m{li}_e{}", EXP[li]),
        10 => "G".into(),
        _ => "D".into(),
    }
}
fn phys(li: usize) -> usize {
    match li {
        0..=9 => 16 + li,
        10 => 27,
        _ => 28,
    }
}
fn per_row(li: usize) -> usize {
    if li < 10 { 1 } else { 4 }
}
fn own_width(li: usize) -> usize {
    if li < 10 { 112 } else { DW }
}
fn d_own(cx: &Ctx, r: usize, x: QM31) -> Vec<M31> {
    flatten(&scale(&cx.gr[r][1..], x))
}
type Src = (Vec<M31>, Vec<W>, Vec<QM31>);
/// z8c `Lanes` (balanced sources: e_r active, e_r - e_0 inactive).
struct Lanes<'a> {
    cx: &'a Ctx,
    rr: Vec<Vec<Vec<QM31>>>,
    zero: Vec<Vec<Src>>,
}
impl<'a> Lanes<'a> {
    fn new(cx: &'a Ctx) -> Self {
        let a = cx.a;
        let rr: Vec<Vec<Vec<QM31>>> = std::thread::scope(|s| {
            let hs: Vec<_> = (0..LANES)
                .map(|li| s.spawn(move || (0..N).map(|r| if li == 11 { tail_row(&a, r) } else { round_row(&a, r, li) }).collect::<Vec<_>>()))
                .collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let mut l = Lanes { cx, rr, zero: vec![] };
        l.zero = (0..LANES).map(|li| (0..per_row(li)).map(|k| l.raw(li, 0, k)).collect()).collect();
        l
    }
    fn raw(&self, li: usize, r: usize, k: usize) -> Src {
        let cx = self.cx;
        if li < 10 {
            (cx.br[r][1..].to_vec(), cx.batched(phys(li), W::ONE, r), self.rr[li][r].clone())
        } else {
            let x = tower(k);
            (d_own(cx, r, x), cx.batched(phys(li), wq(x), r), scale(&self.rr[li][r], x))
        }
    }
    fn count(&self, li: usize) -> usize {
        (N - 1) * per_row(li)
    }
    fn row_of(&self, li: usize, i: usize) -> (usize, usize) {
        (i / per_row(li) + 1, i % per_row(li))
    }
    fn bal(&self, li: usize, i: usize) -> Src {
        let (r, k) = self.row_of(li, i);
        let s = self.raw(li, r, k);
        if !inactive(r) {
            return s;
        }
        let z = &self.zero[li][k];
        (sub_vec(&s.0, &z.0, |x, y| x.sub(y)), sub_vec(&s.1, &z.1, |x, y| x.sub(y)), sub_vec(&s.2, &z.2, |x, y| x.sub(y)))
    }
}
/// z8c `conditioned_sources` (semantic eligible noise balanced vs row 1023, H1
/// padding vs row 0) with the per-pair witness-difference targets.
fn conditioned_sources(cx: &Ctx, traces: &[Trace], pairs: usize, global: &mut Ech<M31>) -> Vec<Vec<M31>> {
    let a = &cx.a;
    let tw = cx.lay.tw;
    let mut sol = vec![vec![M31::ZERO; tw]; pairs];
    for c in 0..16 {
        let rows: Vec<usize> = (0..N).filter(|&r| r != 1023 && eligible(c, r)).collect();
        let tg: Vec<Vec<M31>> = (0..pairs)
            .map(|p| {
                let d: Vec<M31> = (0..N).map(|r| traces[2 * p][c][r].c0.a.sub(traces[2 * p + 1][c][r].c0.a)).collect();
                (1..113).map(|i| (0..N).fold(M31::ZERO, |s, r| s.add(d[r].mul(cx.br[r][i])))).collect()
            })
            .collect();
        let rd = round_row(a, 1023, 38 + c);
        let bd = cx.batched(c, W::ONE, 1023);
        let s = lane_stage(
            rows.len(),
            |i| {
                let r = rows[i];
                let rr = round_row(a, r, 38 + c);
                let bb = cx.batched(c, W::ONE, r);
                if inactive(r) {
                    (sub_vec(&cx.br[r][1..], &cx.br[1023][1..], |x, y| x.sub(y)), carry(&sub_vec(&bb, &bd, |x, y| x.sub(y)), &sub_vec(&rr, &rd, |x, y| x.sub(y))))
                } else {
                    (cx.br[r][1..].to_vec(), carry(&bb, &rr))
                }
            },
            &tg,
            tw,
            global,
        );
        for p in 0..pairs {
            for j in 0..tw {
                sol[p][j] = sol[p][j].add(s[p][j]);
            }
        }
    }
    let rows: Vec<usize> = (1..N).filter(|&r| inactive(r)).collect();
    let tg: Vec<Vec<M31>> = (0..pairs)
        .map(|p| {
            let d: Vec<QM31> = (0..N).map(|r| traces[2 * p][16][r].sub(traces[2 * p + 1][16][r])).collect();
            flatten(&(1..95).map(|i| (0..N).fold(QM31::ZERO, |s, r| s.add(d[r].mul(cx.gr[r][i])))).collect::<Vec<_>>())
        })
        .collect();
    let zero = vec![QM31::ZERO; 271];
    let s = lane_stage(
        4 * rows.len(),
        |i| {
            let (r, k) = (rows[i / 4], i % 4);
            let x = tower(k);
            let b = sub_vec(&cx.batched(26, wq(x), r), &cx.batched(26, wq(x), 0), |p, q| p.sub(q));
            (flatten(&scale(&sub_vec(&cx.gr[r][1..], &cx.gr[0][1..], |p, q| p.sub(q)), x)), carry(&b, &zero))
        },
        &tg,
        tw,
        global,
    );
    for p in 0..pairs {
        for j in 0..tw {
            sol[p][j] = sol[p][j].add(s[p][j]);
        }
    }
    sol
}

// ------------------------------------------------- left-kernel accounting
fn null_space(img: &Ech<M31>) -> Vec<Vec<M31>> {
    let n = img.p.len();
    let mut rows: Vec<Option<Vec<M31>>> = img.p.clone();
    let pivots: Vec<usize> = (0..n).filter(|&i| rows[i].is_some()).collect();
    for (pi, &i) in pivots.iter().enumerate().rev() {
        let ri = rows[i].clone().unwrap();
        for &j in &pivots[..pi] {
            let rj = rows[j].as_mut().unwrap();
            let s = rj[i];
            if s != M31::ZERO {
                for t in i..n {
                    rj[t] = rj[t].sub(s.mul(ri[t]));
                }
            }
        }
    }
    (0..n)
        .filter(|&f| rows[f].is_none())
        .map(|f| {
            let mut v = vec![M31::ZERO; n];
            v[f] = M31::ONE;
            for &p in &pivots {
                v[p] = M31::ZERO.sub(rows[p].as_ref().unwrap()[f]);
            }
            v
        })
        .collect()
}
fn dotm(a: &[M31], b: &[M31]) -> M31 {
    a.iter().zip(b).fold(M31::ZERO, |s, (x, y)| s.add(x.mul(*y)))
}
fn ranges(lay: &Lay, cs: &[usize]) -> String {
    let mut out = vec![];
    let mut i = 0;
    while i < cs.len() {
        let mut j = i;
        while j + 1 < cs.len() && cs[j + 1] == cs[j] + 1 {
            j += 1;
        }
        out.push(if i == j { lay.label(cs[i]) } else { format!("{}..{}", lay.label(cs[i]), lay.label(cs[j])) });
        i = j + 1;
    }
    format!("[{}]", out.join(","))
}
/// Annihilator of a batched image (width bw): per candidate group, whether it
/// holds on the image and how much it adds to the explained span; the
/// unexplained remainder's dimension and coordinate support.
fn explain(label: &str, kind: &str, lay: &Lay, img: &Ech<M31>, groups: &[(String, Vec<Vec<M31>>)]) -> usize {
    let bw = lay.bw;
    let rows = ech_rows(img);
    let ann = bw - img.rank;
    let mut expl = Ech::new(bw);
    let mut parts = vec![];
    for (name, fs) in groups {
        // per relation of the group (8 limb functionals each) count failures
        let mut holds = true;
        for f in fs {
            if rows.iter().any(|r| dotm(f, r) != M31::ZERO) {
                holds = false;
                break;
            }
        }
        let before = expl.rank;
        if holds {
            for f in fs {
                expl.insert(f.clone());
            }
        }
        parts.push(format!("{name}:{}:{}", if holds { "holds" } else { "fails" }, expl.rank - before));
    }
    let unexpl = ann - expl.rank;
    println!(
        "Z9_EXPLAIN {label} kind={kind} image_rank={} annihilator_dim={ann} explained_dim={} unexplained_dim={unexpl} groups=[{}]",
        img.rank,
        expl.rank,
        parts.join(",")
    );
    if unexpl > 0 {
        let mut rest = Ech::new(bw);
        let mut union = std::collections::BTreeSet::new();
        let mut shown = 0;
        for nv in null_space(img) {
            let r = expl.residual(nv);
            if r.iter().any(|x| *x != M31::ZERO) && rest.insert(r.clone()).is_some() {
                let cs: Vec<usize> = (0..lay.nb).filter(|&i| (0..8).any(|m| r[8 * i + m] != M31::ZERO)).collect();
                union.extend(cs.iter().copied());
                if shown < 12 {
                    println!("Z9_EXPLAIN_REST {label} kind={kind} index={shown} support={}", ranges(lay, &cs));
                    shown += 1;
                }
            }
        }
        println!("Z9_EXPLAIN_REST_UNION {label} kind={kind} rank={} support={}", rest.rank, ranges(lay, &union.into_iter().collect::<Vec<_>>()));
    }
    unexpl
}
fn t_rank(img: &Ech<M31>, fs: &[Vec<M31>]) -> usize {
    let rows = ech_rows(img);
    rank_of(rows.len().max(1), fs.iter().map(|f| rows.iter().map(|r| dotm(f, r)).collect()))
}

// ------------------------------------------------------------------ main
pub(super) fn main() {
    let args: Vec<_> = std::env::args().collect();
    let get = |k: &str| args.windows(2).find(|x| x[0] == k).map(|x| x[1].clone());
    let s = get("--structure").expect("--structure");
    let v: usize = get("--vector").expect("--vector").parse().unwrap();
    let gi: usize = get("--gamma").expect("--gamma").parse().unwrap();
    let preflight = args.iter().any(|x| x == "--preflight");
    let start = Instant::now();
    let pi = d18_transport();
    for j in 0..N {
        assert_eq!(usize::from(pi[r1::row(j)]), j, "d18_transport is the inverse of Variant::S2 row");
    }
    z5::set_transport(pi);
    println!("Z9_START structure={s} vector={v} gamma_index={gi} preflight={preflight} payload=R1_S2 transport=D18 folds=2 final_len=64 batching=WideExact balanced=true proxy=false");
    let t = trial(v);
    let a = alpha_for(&s, v, &t.a);
    let label = format!("structure={s} vector={v} gamma={gi}");
    let op = opening_challenges(v, gi);
    assert!(op.gamma.c1() != QM31::ZERO, "gamma outside K4");
    println!("Z9_ALPHA {label} alpha={:?} lambda_dims={:?} good3={} outside_k2={:?}", a.map(l4), lambda_dims(&a), good3(&a), (0..10).map(|i| !in_k2(a[i]) as u8).collect::<Vec<_>>());
    println!("Z9_OPENING {label} gamma={:?} kappa={:?} alpha0={:?} alpha1={:?} rho=not_in_view", op.gamma.to_limbs(), op.kappa.to_limbs(), op.alpha0.to_limbs(), op.alpha1.to_limbs());
    check_tail_and_transport(&a, &t.z);
    let src_active = aspis_statement::pool_v1::pool_v1_pair_forest_copy_active_row_masks_v1().ok();
    let active_matches = src_active == Some(ACTIVE);
    assert!(active_matches, "probe ACTIVE table equals pool_v1_pair_forest_copy_active_row_masks_v1");
    let rows_lo: Vec<usize> = (0..56).map(r1::row).collect();
    let rows_hi: Vec<usize> = (56..1024).map(r1::row).collect();
    assert!(inactive(0), "row 0 copy-inactive (balance row)");
    println!(
        "Z9_LAYOUT {label} active_table_matches_source=true inactive_rows={} row0_coefficient={} d_tail_rows_inactive={} d_tail_rows_active={} row0_in_tail={}",
        (0..N).filter(|&r| inactive(r)).count(),
        pi[0],
        rows_lo.iter().filter(|&&r| inactive(r)).count(),
        rows_lo.iter().filter(|&&r| !inactive(r)).count(),
        rows_lo.contains(&0)
    );
    let lay = Lay::new(&t.qs);
    let distinct_fibres = { let mut f: Vec<usize> = t.qs.iter().map(|u| u / 4).collect(); f.sort(); f.dedup(); f.len() };
    println!("Z9_BATCH_LAYOUT {label} queries={} distinct_folded_fibres={distinct_fibres} folded_values={} batched_E={} batched_limbs={} r0_batched_limbs=2112", t.qs.len(), lay.nf, lay.nb, lay.bw);
    let geo = Geo::new();
    let zk = [[t.z[0].x, t.z[0].y], [t.z[1].x, t.z[1].y]];
    let wts = r1::Weights::new(&a, &zk);
    // Weight layout against the probe's own functionals.
    let pts = points(&a);
    for j in 0..N {
        let r = r1::row(j);
        for k in 0..3 {
            assert_eq!(wts.raw(1 + k, j, inactive_fn), eq(&pts[k], r), "kind {} eq orientation j={j}", 1 + k);
        }
        assert_eq!(wts.raw(4, j, inactive_fn), h_weight(&a, j), "kind 4 libra j={j}");
        for k in 0..2 {
            assert_eq!(wts.raw(5 + k, j, inactive_fn), evalrow(j, t.z[k]), "kind {} ood j={j}", 5 + k);
        }
    }
    println!("Z9_CHECK weights kinds1-3=eq(points,row(j)) kind4=h_weight(j) kinds5-6=evalrow(j,z) ok=true");
    let w = wts.materialize(op.kappa, inactive_fn);
    let phi = unit_functionals(&geo, &w, &op, &lay);
    let beta: Vec<Vec<W>> = (0..N).map(|r| phi[usize::from(pi[r])].clone()).collect();
    for r in 0..N {
        assert_eq!(beta[r][0], if inactive(r) { W::ONE } else { W::ZERO });
    }
    let gpow = (0..29).map(|l| op.gamma.pow(l as u64)).collect();
    let (br, gr) = raw_c(&a, &t.z, &t.qs);
    let tail: Vec<_> = (0..N).map(|r| tail_row(&a, r)).collect();
    let cx = Ctx { a, br, gr, tail, beta, gpow, lay };
    let lay = &cx.lay;
    {
        let mut rng = Rng(0x5a39_f01d ^ v as u64);
        let q1: Vec<W> = (0..256).map(|_| w_uniform(&mut rng)).collect();
        let fw = geo.evaluate(&q1, 0);
        for &i in &lay.fpos {
            let cf = (0..256).fold(W::ZERO, |s, d| s.add(q1[d].mul_m31(geo.unit_eval(d, i))));
            assert_eq!(cf, fw[i], "folded closed form at {i}");
        }
        println!("Z9_CHECK folded_word_closed_form positions={} ok=true", lay.fpos.len());
    }
    pipeline_check(&cx, &geo, &wts, &w, &op, &t.qs, 0x5a39_c0de ^ v as u64);
    let rel = relations(&w, &op, &t.qs, lay);
    let bw = lay.bw;
    let groups: Vec<(String, Vec<Vec<M31>>)> = vec![
        ("ia".into(), rel.ia.limb_functionals(bw)),
        ("S2a".into(), rel.s2a.limb_functionals(bw)),
        ("S2b".into(), rel.s2b.limb_functionals(bw)),
        ("S1".into(), rel.s1.limb_functionals(bw)),
        ("C".into(), rel.cu.iter().flat_map(|r| r.limb_functionals(bw)).collect()),
        ("L".into(), rel.lu.iter().flat_map(|r| r.limb_functionals(bw)).collect()),
    ];
    let mut groups_low = groups.clone();
    for r in &rel.low {
        groups_low.push((r.name.clone(), r.limb_functionals(bw)));
    }
    let nrel = 4 + 2 * t.qs.len();
    println!("Z9_SETUP {label} relations_E={nrel} relation_limbs={} predicted_dim_B0={} seconds={:.3}", 8 * nrel, bw - 8 * nrel, start.elapsed().as_secs_f64());
    let ln = Lanes::new(&cx);

    // ---- Pass 1: per-lane own kernels carrying [batched | round]; global gate. ----
    let tw = lay.tw;
    let mut pure = Ech::new(tw);
    let mut rker: Vec<Ech<M31>> = vec![];
    let mut viol = [0usize; 6];
    let mut carries_checked = 0usize;
    for li in 0..LANES {
        let mut rk = Ech::new(RW);
        let mut ker = 0;
        let n = ln.count(li);
        lane_elim(
            n,
            |i| {
                let (o, b, r) = ln.bal(li, i);
                (o, carry(&b, &r))
            },
            |c| {
                ker += 1;
                let y = wvals(&c[..bw]);
                carries_checked += 1;
                if rel.ia.eval(&y) != W::ZERO { viol[0] += 1; }
                if rel.s2a.eval(&y) != W::ZERO { viol[1] += 1; }
                if rel.s2b.eval(&y) != W::ZERO { viol[2] += 1; }
                if rel.s1.eval(&y) != W::ZERO { viol[3] += 1; }
                if rel.cu.iter().any(|r| r.eval(&y) != W::ZERO) { viol[4] += 1; }
                if rel.lu.iter().any(|r| r.eval(&y) != W::ZERO) { viol[5] += 1; }
                rk.insert(c[bw..].to_vec());
                pure.insert(c);
            },
        );
        println!(
            "Z9_LANE_OWN {label} lane={} sources={n} own_rank={} own_functionals={} round_image_of_own_kernel={} seconds={:.3}",
            lane_name(li), n - ker, own_width(li), rk.rank, start.elapsed().as_secs_f64()
        );
        rker.push(rk);
    }
    println!(
        "Z9_RELATIONS {label} carries_checked={carries_checked} violations_ia={} violations_S2a={} violations_S2b={} violations_S1={} violations_C={} violations_L={} relations_annihilate_exactly={}",
        viol[0], viol[1], viol[2], viol[3], viol[4], viol[5], viol.iter().all(|x| *x == 0)
    );
    if viol.iter().any(|x| *x != 0) {
        println!("STOP reason=verifier_relation_not_annihilating {label} violations={viol:?}");
    }
    let ia_pivots = (0..8).filter(|&i| pure.p[i].is_some()).count();
    let batched_rank = (0..bw).filter(|&i| pure.p[i].is_some()).count();
    let retained = slice_image(&pure, bw, bw);
    let silent = slice_image(&pure, bw + 4, bw);
    let mut rown = Ech::new(RW);
    for rk in &rker {
        for row in ech_rows(rk) {
            rown.insert(row);
        }
    }
    let rown_zero = initial_zero(copied_ech(&rown));
    println!(
        "Z9_GATE_PURE {label} span_rank={} batched_pivots={batched_rank} ia_pivots={ia_pivots} initial_retained_rank={} silent_rank={} chain0_dim=1076 seconds={:.3}",
        pure.rank, retained.rank, silent.rank, start.elapsed().as_secs_f64()
    );
    println!("Z9_QPRIME {label} round_image_of_ker_own_initial_retained={} initial_zero={}", rown.rank, rown_zero.rank);
    let b0 = batched_rank - ia_pivots;
    let b_kr = pure.rank - rown.rank;
    println!(
        "Z9_BCOND {label} bat_rank_on_ker_own={b0} bat_rank_on_ker_own_and_ker_R={b_kr} bcond_holds={} predicted_dim_B0={} (second = span_rank - dim R(ker own) = {} - {})",
        b0 == b_kr, bw - 8 * nrel, pure.rank, rown.rank
    );
    report(&label, "silent", silent.rank, &Proj::of(&silent, &a));
    report(&label, "silent_initial_retained", retained.rank, &Proj::of(&retained, &a));
    report(&label, "round_image_of_ker_own", rown.rank, &Proj::of(&rown, &a));
    if silent.rank < 1076 {
        println!("Z9_FINDING {label} silent_rank={} below=1076 deficit={}", silent.rank, 1076 - silent.rank);
    }
    let chain0: Vec<Vec<M31>> = (4..RW)
        .map(|i| {
            let mut u = vec![M31::ZERO; RW];
            u[i] = M31::ONE;
            let q = unflat(&u);
            let ph = final_value(&q, &a);
            flatten(&normalize_d(&q, ph, &a).expect("alpha9=1/2"))
        })
        .collect();
    summarize(&format!("{label} chain0_basis"), &silent, &chain0);
    summarize(&format!("{label} qprime_chain0_basis"), &rown_zero, &chain0);
    let mut img_b0 = Ech::new(bw);
    for row in pure.p.iter().take(bw).flatten() {
        img_b0.insert(row[..bw].to_vec());
    }
    explain(&label, "bat_on_ker_own", lay, &img_b0, &groups_low);
    println!("Z9_PASS1_DONE {label} seconds={:.3}", start.elapsed().as_secs_f64());

    // ---- D23 decomposition on R1: V_D, V_G, assembly. ----
    for &r in &rows_hi {
        assert!(ln.rr[11][r].iter().all(|x| *x == QM31::ZERO), "D coefficient >= 56 has a round contribution");
    }
    let s0 = *rows_hi.iter().find(|&&r| inactive(r)).expect("an inactive D-high row");
    let img_d = {
        let mut srcs: Vec<(usize, usize, bool)> = vec![];
        for &r in &rows_hi {
            if r == s0 {
                continue;
            }
            for k in 0..4 {
                srcs.push((r, k, inactive(r)));
            }
        }
        let mut img = Ech::new(bw);
        lane_elim(
            srcs.len(),
            |i| {
                let (r, k, sub) = srcs[i];
                let (o, b, _) = ln.raw(11, r, k);
                if sub {
                    let (o0, b0, _) = ln.raw(11, s0, k);
                    (sub_vec(&o, &o0, |x, y| x.sub(y)), wflat(&sub_vec(&b, &b0, |x, y| x.sub(y))))
                } else {
                    (o, wflat(&b))
                }
            },
            |c| {
                img.insert(c);
            },
        );
        img
    };
    let flo = |img: &Ech<M31>, e: usize| rank_of(8 * e, ech_rows(img).iter().map(|r| r[8 * lay.fin(0)..8 * lay.fin(e)].to_vec()));
    println!(
        "Z9_VD {label} base_row={s0} bat_rank={} f0_3_rank={} f0_2_rank={} f3_rank={} predicted={}",
        img_d.rank,
        flo(&img_d, 4),
        flo(&img_d, 3),
        rank_of(8, ech_rows(&img_d).iter().map(|r| r[8 * lay.fin(3)..8 * lay.fin(4)].to_vec())),
        bw - 8 * nrel - 24
    );
    explain(&label, "V_D", lay, &img_d, &groups_low);
    let mut img_g = Ech::new(bw);
    let mut gker = 0;
    lane_elim(
        ln.count(10),
        |i| {
            let (o, b, rd) = ln.bal(10, i);
            let mut vv = o;
            vv.extend(flatten(&rd));
            (vv, wflat(&b))
        },
        |c| {
            gker += 1;
            img_g.insert(c);
        },
    );
    let mut asm = copied_ech(&img_d);
    for row in ech_rows(&img_g) {
        asm.insert(row);
    }
    let mut asm_in_b0 = copied_ech(&img_b0);
    for row in ech_rows(&asm) {
        asm_in_b0.insert(row);
    }
    println!(
        "Z9_VG {label} kernel_dim={gker} bat_rank={} f0_3_rank={} assembly_rank={} dim_B0={} assembly_inside_B0={} b0_equals_vd_plus_vg={}",
        img_g.rank,
        flo(&img_g, 4),
        asm.rank,
        img_b0.rank,
        asm_in_b0.rank == img_b0.rank,
        asm.rank == img_b0.rank && asm_in_b0.rank == img_b0.rank
    );
    explain(&label, "V_G", lay, &img_g, &groups_low);
    // Z8b-style PCS block: D's coefficients >= 56, unbalanced, onto [batched | D own].
    {
        let (mut full, mut bat_on_ker) = (Ech::new(bw + DW), Ech::new(bw));
        for &r in &rows_hi {
            for k in 0..4 {
                let (o, b, _) = ln.raw(11, r, k);
                let mut x = wflat(&b);
                x.extend(o);
                full.insert(x);
            }
        }
        lane_elim(
            rows_hi.len() * 4,
            |i| {
                let (o, b, _) = ln.raw(11, rows_hi[i / 4], i % 4);
                (o, wflat(&b))
            },
            |c| {
                bat_on_ker.insert(c);
            },
        );
        println!(
            "Z9_PCS_BLOCK {label} dhigh_unbalanced_sources={} rank_bat_plus_d_own={} of={} bat_rank_on_ker_own_D={} ia_pivots={}",
            rows_hi.len() * 4,
            full.rank,
            bw + DW,
            bat_on_ker.rank,
            (0..8).filter(|&i| bat_on_ker.p[i].is_some()).count()
        );
    }
    println!("Z9_D23_DONE {label} seconds={:.3}", start.elapsed().as_secs_f64());
    if preflight {
        println!("Z9_PREFLIGHT_DONE {label} wall_seconds={:.3}", start.elapsed().as_secs_f64());
        return;
    }

    // ---- (i') and (ii') (copied from z8c, tags renamed). ----
    let (pubdata, instances) = real::instances();
    let ch = t.ch;
    let traces: Vec<Trace> = instances
        .iter()
        .map(|w| {
            let mut tr: Trace = w.compilation.semantic_c1.c1.iter().map(|col| col.iter().map(|x| QM31::from_m31(*x)).collect()).collect();
            match build_pool_v1_pair_forest_copy_helper_v1(&w.compilation.trace, w.compilation.public_statement.live_snapshot.next_pair_index, ch.lambda, ch.chi) {
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
        println!("Z9_TERMINAL {label} pair={pair} pinned={:?} derivative={:?} ii={:?}", l4(original.terminal[0]), l4(original.terminal[1]), l4(original.terminal[2]));
        targets.push(normalized(&original, &a, &traces[2 * pair], &traces[2 * pair + 1], &ch, public));
    }
    let ip_t: Vec<_> = targets.iter().map(|t| flatten(&t.pinned)).collect();
    let derivative: Vec<_> = targets.iter().map(|t| flatten(&t.derivative)).collect();
    summarize(&format!("{label} r1_i_prime"), &silent, &ip_t);
    summarize(&format!("{label} r1_derivative_diagnostic"), &silent, &derivative);
    let mut full = Ech { p: pure.p.clone(), rank: pure.rank };
    let sol = conditioned_sources(&cx, &traces, 5, &mut full);
    let conditioned = slice_image(&full, bw, bw);
    let mut ii = vec![];
    let mut batched_unmatched = vec![];
    for p in 0..5 {
        let mut b = vec![W::ZERO; lay.nb];
        for c in 0..17 {
            let lane = if c == 16 { 26 } else { c };
            for r in 0..N {
                let d = traces[2 * p][c][r].sub(traces[2 * p + 1][c][r]);
                if d == QM31::ZERO {
                    continue;
                }
                for (e, x) in b.iter_mut().zip(cx.batched(lane, wq(d), r)) {
                    *e = e.add(x);
                }
            }
        }
        let target = carry(&b, &targets[p].difference);
        let residual = batched_reduce(&full, sub_vec(&target, &sol[p], |x, y| x.sub(y)), bw);
        let unmatched = residual[..bw].iter().filter(|x| **x != M31::ZERO).count();
        batched_unmatched.push(unmatched);
        ii.push(residual[bw..].to_vec());
    }
    println!("Z9_II_BATCHED {label} batched_coordinates_unmatched_per_pair={batched_unmatched:?}");
    summarize(&format!("{label} r1_ii_prime"), &conditioned, &ii);
    let ip = pass_count(&silent, &ip_t);
    let iip = (0..5).filter(|&p| batched_unmatched[p] == 0 && conditioned.residual(ii[p].clone()).iter().all(|x| *x == M31::ZERO)).count();
    println!(
        "Z9_GATE {label} silent_rank={} initial_retained_rank={} full_span_rank={} full_conditioned_rank={} i_pass={ip} ii_pass={iip} attempted=5",
        silent.rank, retained.rank, full.rank, conditioned.rank
    );
    println!("Z9_DONE {label} wall_seconds={:.3}", start.elapsed().as_secs_f64());
}
