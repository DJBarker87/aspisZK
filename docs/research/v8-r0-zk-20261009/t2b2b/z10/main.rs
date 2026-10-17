//! Z10 — reduced-model failure-rate probe for the OT-open transversality shape.
//! Research probe only; not protocol code.  Model (see STUDY-TRANSVERSALITY-R1 §A):
//! one F-valued (M31) mask lane of 1,024 rows = natural coefficients (via a
//! transport pi), K4 = QM31 challenges, query-free functional space
//!   V = rowspace(R_l) (10 sumcheck rounds, exponent e, limbs over F)
//!     + 3 eq-MLE claims + Libra extra (k < 56) + 2 OOD evaluations + sigma,
//! and the 88 evaluation functionals at the children of 22 queried fibres of
//! the 2^20-point canonic circle coset.  FAIL <=> rank(V + E) < rank V + 88.
use std::env;

const P: u64 = (1u64 << 31) - 1;
#[inline] fn md(a: u64) -> u64 { let x = (a & P) + (a >> 31); if x >= P { x - P } else { x } }
#[inline] fn mul(a: u64, b: u64) -> u64 { md(md(a * b)) }
#[inline] fn add(a: u64, b: u64) -> u64 { let s = a + b; if s >= P { s - P } else { s } }
#[inline] fn sub(a: u64, b: u64) -> u64 { if a >= b { a - b } else { a + P - b } }
fn pw(mut a: u64, mut e: u64) -> u64 { let mut r = 1; while e > 0 { if e & 1 == 1 { r = mul(r, a); } a = mul(a, a); e >>= 1; } r }
fn inv(a: u64) -> u64 { pw(a, P - 2) }

// CM31 = F[i]/(i^2+1), QM31 = CM31[u]/(u^2 - (2+i)).
#[derive(Clone, Copy, PartialEq, Debug)] struct C(u64, u64);
#[derive(Clone, Copy, PartialEq, Debug)] struct Q(C, C);
impl C {
    fn add(self, o: C) -> C { C(add(self.0, o.0), add(self.1, o.1)) }
    fn sub(self, o: C) -> C { C(sub(self.0, o.0), sub(self.1, o.1)) }
    fn mul(self, o: C) -> C { C(sub(mul(self.0, o.0), mul(self.1, o.1)), add(mul(self.0, o.1), mul(self.1, o.0))) }
    fn inv(self) -> C { let n = inv(add(mul(self.0, self.0), mul(self.1, self.1))); C(mul(self.0, n), mul(sub(0, self.1), n)) }
}
const R: C = C(2, 1);
impl Q {
    fn f(a: u64) -> Q { Q(C(a, 0), C(0, 0)) }
    fn add(self, o: Q) -> Q { Q(self.0.add(o.0), self.1.add(o.1)) }
    fn sub(self, o: Q) -> Q { Q(self.0.sub(o.0), self.1.sub(o.1)) }
    fn mul(self, o: Q) -> Q { Q(self.0.mul(o.0).add(R.mul(self.1.mul(o.1))), self.0.mul(o.1).add(self.1.mul(o.0))) }
    fn inv(self) -> Q { let d = self.0.mul(self.0).sub(R.mul(self.1.mul(self.1))).inv(); Q(self.0.mul(d), C(0, 0).sub(self.1).mul(d)) }
    fn limbs(self) -> [u64; 4] { [self.0 .0, self.0 .1, self.1 .0, self.1 .1] }
}
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 { self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15); let mut z = self.0; z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9); z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb); z ^ (z >> 31) }
    fn f(&mut self) -> u64 { self.next() % P }
    fn q(&mut self) -> Q { Q(C(self.f(), self.f()), C(self.f(), self.f())) }
    fn below(&mut self, n: u64) -> u64 { self.next() % n }
}

// Circle group over M31 (and over QM31 for OOD points).
fn cmul(a: (u64, u64), b: (u64, u64)) -> (u64, u64) { (sub(mul(a.0, b.0), mul(a.1, b.1)), add(mul(a.0, b.1), mul(a.1, b.0))) }
fn cpow(mut a: (u64, u64), mut e: u64) -> (u64, u64) { let mut r = (1, 0); while e > 0 { if e & 1 == 1 { r = cmul(r, a); } a = cmul(a, a); e >>= 1; } r }
const GEN: (u64, u64) = (2, 1268011823); // order 2^31

/// Natural-basis value of message index m at (x, y): y^(m&1) * prod_{b in bits(m>>1)} T_{2^b}(x).
fn nat_row_f(x: u64, y: u64) -> Vec<u64> {
    let mut t = [0u64; 9]; t[0] = x; for b in 1..9 { t[b] = sub(add(mul(t[b - 1], t[b - 1]), mul(t[b - 1], t[b - 1])), 1); }
    let mut n = vec![1u64; 512];
    for j in 1..512usize { let b = j.trailing_zeros() as usize; n[j] = mul(n[j & !(1 << b)], t[b]); }
    let mut out = vec![0u64; 1024];
    for m in 0..1024 { out[m] = if m & 1 == 1 { mul(y, n[m >> 1]) } else { n[m >> 1] }; }
    out
}
fn nat_row_q(x: Q, y: Q) -> Vec<Q> {
    let mut t = [Q::f(0); 9]; t[0] = x; for b in 1..9 { t[b] = t[b - 1].mul(t[b - 1]).add(t[b - 1].mul(t[b - 1])).sub(Q::f(1)); }
    let mut n = vec![Q::f(1); 512];
    for j in 1..512usize { let b = j.trailing_zeros() as usize; n[j] = n[j & !(1 << b)].mul(t[b]); }
    (0..1024).map(|m| if m & 1 == 1 { y.mul(n[m >> 1]) } else { n[m >> 1] }).collect()
}

/// Row-echelon basis over F; returns (rows, pivot column per row).
struct Basis { rows: Vec<Vec<u64>>, piv: Vec<usize> }
impl Basis {
    fn new() -> Self { Basis { rows: vec![], piv: vec![] } }
    fn reduce(&self, v: &mut [u64]) { for (r, &p) in self.rows.iter().zip(&self.piv) { let c = v[p]; if c != 0 { for k in 0..v.len() { if r[k] != 0 { v[k] = sub(v[k], mul(c, r[k])); } } } } }
    fn insert(&mut self, mut v: Vec<u64>) -> bool {
        self.reduce(&mut v);
        if let Some(p) = v.iter().position(|&x| x != 0) { let s = inv(v[p]); for x in v.iter_mut() { *x = mul(*x, s); } self.rows.push(v); self.piv.push(p); true } else { false }
    }
}


/// Rank over QM31 of a dense matrix (rows of Q).
fn qrank(mut m: Vec<Vec<Q>>) -> usize {
    let cols = if m.is_empty() { 0 } else { m[0].len() }; let mut rank = 0;
    for c in 0..cols {
        let Some(p) = (rank..m.len()).find(|&i| m[i][c] != Q::f(0)) else { continue };
        m.swap(rank, p); let iv = m[rank][c].inv();
        for k in 0..cols { m[rank][k] = m[rank][k].mul(iv); }
        for i in 0..m.len() { if i != rank && m[i][c] != Q::f(0) { let f = m[i][c]; for k in 0..cols { let t = f.mul(m[rank][k]); m[i][k] = m[i][k].sub(t); } } }
        rank += 1;
    }
    rank
}

/// Route M2 residual (STUDY §3.3): Kronecker/Hankel certificate shape for the three
/// eq-MLE claims of a Libra lane restricted to the reservoir block N'_128 * P_{<128}
/// of one channel, identity transport (rows = natural indices; INDICATIVE ONLY —
/// the release certificate needs the real R1 transport).  With 22 nodes + 2 OOD +
/// sigma's point t = 1 (25 rank-one functionals), the certificate is
///   rank_K4 [H_{eta_1}J | H_{eta_2}J | H_{eta_3}J] = 3*26,
/// H_eta(a, b) = eta(t^(a+b)), a < 100, b in J = {0..25}.
fn kron(trials: usize, seed: u64, control: bool) {
    let mut rng = Rng(seed);
    // monomial coefficients of N'_e(t) = prod_{b in bits e} T_{2^b}(t), e < 128
    let mut tpoly: Vec<Vec<u64>> = vec![vec![0, 1]]; // T_1 = t
    for b in 1..7 { let prev = &tpoly[b - 1]; let mut sq = vec![0u64; prev.len() * 2 - 1];
        for i in 0..prev.len() { for j in 0..prev.len() { sq[i + j] = add(sq[i + j], mul(prev[i], prev[j])); } }
        for x in sq.iter_mut() { *x = add(*x, *x); } sq[0] = sub(sq[0], 1); tpoly.push(sq); }
    let mut nmono = vec![vec![0u64; 128]; 128]; nmono[0][0] = 1;
    for e in 1..128usize { let b = e.trailing_zeros() as usize; let base = nmono[e & !(1 << b)].clone(); let tp = &tpoly[b];
        let mut out = vec![0u64; 128]; for i in 0..128 { if base[i] != 0 { for j in 0..tp.len() { if i + j < 128 { out[i + j] = add(out[i + j], mul(base[i], tp[j])); } } } } nmono[e] = out; }
    // C[k][e]: N'-coefficient e of t^k.  Solve sum_e C[k][e] nmono[e] = t^k by back substitution (nmono[e] has degree e, leading coeff != 0).
    let mut cmat = vec![vec![0u64; 128]; 128];
    for k in 0..128 { let mut rem = vec![0u64; 128]; rem[k] = 1;
        for e in (0..128).rev() { if rem[e] != 0 { let f = mul(rem[e], inv(nmono[e][e])); cmat[k][e] = f; for i in 0..=e { rem[i] = sub(rem[i], mul(f, nmono[e][i])); } } } }
    for tr in 0..trials {
        let alpha: Vec<Q> = (0..10).map(|_| rng.q()).collect();
        let p1: Vec<Q> = (0..10).map(|_| rng.q()).collect();
        let mut p2 = alpha.clone(); p2[6] = Q::f(1).sub(p2[6]); p2[7] = Q::f(1).sub(p2[7]);
        let mut s: Vec<Vec<Q>> = vec![vec![Q::f(0); 78]; 100];
        for (kk, pt) in [&alpha, &p1, &p2].iter().enumerate() {
            // eta_e = eq over the 7 d-bits (row bits 2..8) of the block coordinate e
            let mut eta: Vec<Q> = (0..128).map(|e: usize| (0..7).fold(Q::f(1), |acc, b| acc.mul(if (e >> b) & 1 == 1 { pt[2 + b] } else { Q::f(1).sub(pt[2 + b]) }))).collect();
            // control: replace the first functional by an evaluation at a random F point (Hankel rank 1); expected rank 26*2 + 1 = 53
            if control && kk == 0 { let t0 = rng.f(); eta = (0..128).map(|e| Q::f((0..128).fold(0u64, |acc, i| add(acc, mul(nmono[e][i], pw(t0, i as u64)))))).collect(); }
            let mom: Vec<Q> = (0..128).map(|k| (0..128).fold(Q::f(0), |acc, e| acc.add(eta[e].mul(Q::f(cmat[k][e]))))).collect();
            for a in 0..100 { for b in 0..26 { s[a][26 * kk + b] = mom[a + b]; } }
        }
        let r = qrank(s);
        println!("KRON trial={} rank={} of 78 {}", tr, r, if r == 78 { "OK" } else { "DEFICIENT" });
    }
}

fn main() {
    let a: Vec<String> = env::args().collect();
    if a.get(1).map(|x| x == "kron").unwrap_or(false) { kron(a.get(2).map(|s| s.parse().unwrap()).unwrap_or(5), a.get(3).map(|s| s.parse().unwrap()).unwrap_or(1), a.get(4).map(|x| x == "control").unwrap_or(false)); return; }
    let e: usize = a.get(1).map(|s| s.parse().unwrap()).unwrap_or(21);      // exponent; 26 = G-shape factor 1+Y^26
    let pimode: &str = a.get(2).map(|s| s.as_str()).unwrap_or("id");        // id | rand | rev
    let trials: usize = a.get(3).map(|s| s.parse().unwrap()).unwrap_or(200);
    let qmode: &str = a.get(4).map(|s| s.as_str()).unwrap_or("uniform");   // uniform | coset | consecutive | pairs
    let seed: u64 = a.get(5).map(|s| s.parse().unwrap()).unwrap_or(1);
    let extra_pad: usize = a.get(6).map(|s| s.parse().unwrap()).unwrap_or(0); // extra generic functionals added to V
    let mut rng = Rng(seed);
    // transport pi: row -> coefficient
    let mut pi: Vec<usize> = (0..1024).collect();
    if pimode == "rand" { for i in (1..1024).rev() { let j = rng.below(i as u64 + 1) as usize; pi.swap(i, j); } }
    if pimode == "rev" { for r in 0..1024usize { pi[r] = (0..10).fold(0, |acc, b| acc | (((r >> b) & 1) << (9 - b))); } }
    let gshape = e == 26;
    let w: Vec<u64> = (0..10).map(|j| if gshape { 275 + 150 * j as u64 } else { 3 + 22 * j as u64 }).collect();
    let alpha: Vec<Q> = (0..10).map(|_| rng.q()).collect();
    let bit = |r: usize, i: usize| (r >> i) & 1;
    let mut fun: Vec<Vec<Q>> = vec![]; // K4-valued functionals on rows
    // rounds
    let mut binom = vec![vec![0u64; 28]; 28];
    for n in 0..28 { binom[n][0] = 1; for k in 1..=n { binom[n][k] = add(binom[n - 1][k - 1], if k < n { binom[n - 1][k] } else { 0 }); } }
    for j in 0..(if e == 0 { 0 } else { 10 }) {
        let cj = (0..j).fold(Q::f(0), |s, i| s.add(alpha[i].mul(Q::f(w[i]))));
        let deg = e + 1;
        let mut coef = vec![vec![Q::f(0); 1024]; deg + 1];
        for r in 0..1024 {
            let eqp = (0..j).fold(Q::f(1), |s, i| s.mul(if bit(r, i) == 1 { alpha[i] } else { Q::f(1).sub(alpha[i]) }));
            let beta = (j + 1..10).fold(cj, |s, i| if bit(r, i) == 1 { s.add(Q::f(w[i])) } else { s });
            // (w_j X + beta)^e  (G-shape: 1 + (w_j X + beta)^26)
            let mut pe = vec![Q::f(0); e + 1];
            let mut bp = vec![Q::f(1); e + 1]; for k in 1..=e { bp[k] = bp[k - 1].mul(beta); }
            for k in 0..=e { pe[k] = Q::f(mul(binom[e][k], pw(w[j], k as u64))).mul(bp[e - k]); }
            if gshape { pe[0] = pe[0].add(Q::f(1)); }
            // times (r_j ? X : 1 - X)
            for k in 0..=e {
                if bit(r, j) == 1 { coef[k + 1][r] = coef[k + 1][r].add(eqp.mul(pe[k])); }
                else { coef[k][r] = coef[k][r].add(eqp.mul(pe[k])); coef[k + 1][r] = coef[k + 1][r].sub(eqp.mul(pe[k])); }
            }
        }
        fun.extend(coef);
    }
    let nround = fun.len();
    // claims at alpha, a second random point, and xor12(alpha)
    let p1: Vec<Q> = (0..10).map(|_| rng.q()).collect();
    let mut p2 = alpha.clone(); p2[6] = Q::f(1).sub(p2[6]); p2[7] = Q::f(1).sub(p2[7]);
    for pt in [&alpha, &p1, &p2] { fun.push((0..1024).map(|r| (0..10).fold(Q::f(1), |s, i| s.mul(if bit(r, i) == 1 { pt[i] } else { Q::f(1).sub(pt[i]) }))).collect()); }
    // sigma: 810 inactive rows incl. row 0
    let mut rows: Vec<usize> = (1..1024).collect(); for i in (1..rows.len()).rev() { let j = rng.below(i as u64 + 1) as usize; rows.swap(i, j); }
    let mut sig = vec![Q::f(0); 1024]; sig[0] = Q::f(1); for &r in &rows[..809] { sig[r] = Q::f(1); }
    // functionals on coefficients: c[pi[r]] = u[r]
    let mut vb = Basis::new();
    let mut push_coeff = |vb: &mut Basis, fc: &Vec<Q>| { let mut l = vec![vec![0u64; 1024]; 4]; for k in 0..1024 { let x = fc[k].limbs(); for t in 0..4 { l[t][k] = x[t]; } } for v in l { vb.insert(v); } };
    for f in &fun { let mut fc = vec![Q::f(0); 1024]; for r in 0..1024 { fc[pi[r]] = f[r]; } push_coeff(&mut vb, &fc); }
    if e == 0 { for k in 0..56 { let mut v = vec![0u64; 1024]; v[k] = 1; vb.insert(v); } } // D-shape: Libra rounds read coefficients < 56 only
    let rank_rounds_claims = vb.rows.len();
    { let mut fc = vec![0u64; 1024]; for r in 0..1024 { fc[pi[r]] = sig[r].limbs()[0]; } vb.insert(fc); }
    // Libra extra on coefficients k < 56: alpha_{8+k/28}^{k%28}
    { let mut fc = vec![Q::f(0); 1024]; for k in 0..56 { let base = alpha[8 + k / 28]; let mut v = Q::f(1); for _ in 0..k % 28 { v = v.mul(base); } fc[k] = v; } push_coeff(&mut vb, &fc); }
    // OOD at two random QM31 circle points ((1-t^2)/(1+t^2), 2t/(1+t^2))
    for _ in 0..2 { let t = rng.q(); let d = Q::f(1).add(t.mul(t)).inv(); let x = Q::f(1).sub(t.mul(t)).mul(d); let y = t.add(t).mul(d); push_coeff(&mut vb, &nat_row_q(x, y)); }
    for _ in 0..extra_pad { let v: Vec<u64> = (0..1024).map(|_| rng.f()).collect(); vb.insert(v); }
    let r = vb.rows.len();
    println!("CONFIG e={} gshape={} pi={} qmode={} seed={} pad={} nround_rows={} rank_rounds_claims={} rankV={} margin={}", e, gshape, pimode, qmode, seed, extra_pad, nround, rank_rounds_claims, r, 1024 as i64 - r as i64 - 88);
    // canonic coset points: g^(2i+1), g of order 2^21; fibre = {(x,y),(x,-y),(-x,-y),(-x,y)}
    let g = cpow(GEN, 1 << 10);
    let mut fails = 0usize; let mut minres = usize::MAX;
    for tr in 0..trials {
        let mut xs: Vec<u64> = vec![]; let mut pts: Vec<(u64, u64)> = vec![];
        let i0 = rng.below(1 << 20);
        let mut k = 0u64;
        while pts.len() < 22 {
            let i = match qmode { "coset" => (i0 + k * (1 << 14)) % (1 << 20), "consecutive" => (i0 + k) % (1 << 20), _ => rng.below(1 << 20) };
            k += 1;
            let p = cpow(g, 2 * i + 1);
            let x2 = mul(p.0, p.0);
            if xs.contains(&x2) { continue; }
            xs.push(x2); pts.push(p);
        }
        let mut eb = Basis::new(); let mut indep = 0usize;
        for &(x, y) in &pts {
            for (sx, sy) in [(x, y), (x, sub(0, y)), (sub(0, x), sub(0, y)), (sub(0, x), y)] {
                let mut v = nat_row_f(sx, sy); vb.reduce(&mut v); if eb.insert(v) { indep += 1; }
            }
        }
        if indep < 88 { fails += 1; println!("FAIL trial={} indep={}", tr, indep); }
        minres = minres.min(indep);
        if tr % 50 == 0 { eprintln!("trial {} indep {}", tr, indep); }
    }
    println!("RESULT e={} pi={} qmode={} seed={} pad={} rankV={} trials={} fails={} min_indep={}", e, pimode, qmode, seed, extra_pad, r, trials, fails, minres);
}
