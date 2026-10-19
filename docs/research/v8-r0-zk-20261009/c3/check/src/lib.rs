//! Extraction-friendly P_R1 certificate checker (LOG D38.5, D49.4 C3; zf1/DESIGN-P-CERT.txt §6).
//!
//! The checking side of z4/z9c.rs `check`, restated for Charon/Aeneas:
//! no_std + alloc, monomorphic, u32 limbs and u64 accumulators, flat slices,
//! plain `while` loops, no closures or iterator adapters, one loop nest per
//! function, every failure a `false` (no early return from loops).  Arithmetic
//! is checked (`overflow-checks = true`), so an overflow or out-of-range index
//! panics, which the extraction models as failure: only `check = true` is used.
//!
//! Inputs.  `Pub` is the public column data that the builders compute from the
//! challenges (own/round/bat columns of the referenced sources, the relR1 limb
//! functionals, the ChainT0K4 targets, the lift observation matrices); `Cert`
//! is the certificate.  The checker never eliminates; every test is a dot
//! product over M31 compared with a supplied value, or an index identity.
//! Supplied-and-verified intermediate values (rho, E, beta, the n_f matrix and
//! the lift identity) keep every test a pure "for all i, j" equality.
#![no_std]
extern crate alloc;
use alloc::vec::Vec;

/// The M31 modulus.
pub const P: u64 = 0x7fff_ffff;

/// sum_{p<n} a[ao + p*ast] * b[bo + p*bst], reduced mod P.
pub fn dot(a: &[u32], ao: usize, ast: usize, b: &[u32], bo: usize, bst: usize, n: usize) -> u64 {
    let mut acc: u64 = 0;
    let mut p: usize = 0;
    while p < n {
        let x = a[ao + p * ast] as u64;
        let y = b[bo + p * bst] as u64;
        acc = acc + x * y % P;
        p += 1;
    }
    acc % P
}

/// Gathered dot: sum_{p<n} m[idx[io+p]*st + i] * c[co+p], reduced mod P.
pub fn kdot(m: &[u32], st: usize, i: usize, idx: &[u32], io: usize, c: &[u32], co: usize, n: usize) -> u64 {
    let mut acc: u64 = 0;
    let mut p: usize = 0;
    while p < n {
        let t = idx[io + p] as usize;
        let x = m[t * st + i] as u64;
        let y = c[co + p] as u64;
        acc = acc + x * y % P;
        p += 1;
    }
    acc % P
}

/// Kernel-entry coordinates (Lean `kcoord`): for every row i < nrows,
/// m[j*st+i] + sum_p m[idx[io+p]*st+i] * c[co+p] == tgt[to + i*ts] (mod P).
/// A kernel test passes tgt = [0] with ts = 0.
pub fn kimg_ok(
    m: &[u32],
    st: usize,
    nrows: usize,
    j: usize,
    idx: &[u32],
    io: usize,
    c: &[u32],
    co: usize,
    s: usize,
    tgt: &[u32],
    to: usize,
    ts: usize,
) -> bool {
    let mut ok = true;
    let mut i: usize = 0;
    while i < nrows {
        let v = (m[j * st + i] as u64 + kdot(m, st, i, idx, io, c, co, s)) % P;
        if v != tgt[to + i * ts] as u64 {
            ok = false;
        }
        i += 1;
    }
    ok
}

/// Pivot indices of one entry: idx[io+p] < nsrc and in the entry's lane.
pub fn piv_ok(idx: &[u32], io: usize, s: usize, lane: &[u32], lj: u32, nsrc: usize) -> bool {
    let mut ok = true;
    let mut p: usize = 0;
    while p < s {
        let t = idx[io + p] as usize;
        if t >= nsrc {
            ok = false;
        } else if lane[t] != lj {
            ok = false;
        }
        p += 1;
    }
    ok
}

/// A family of kernel entries (j, s, pivot offset, coefficient offset):
/// zero z1-coordinates (rows wl[lane j]), zero z2-coordinates (n2 rows),
/// and g-coordinates (ng rows) equal to out[e*ng ..].
pub fn ents_ok(
    ej: &[u32],
    es: &[u32],
    epo: &[u32],
    eco: &[u32],
    idx: &[u32],
    coef: &[u32],
    m: usize,
    lane: &[u32],
    wl: &[u32],
    nsrc: usize,
    z1: &[u32],
    s1: usize,
    z2: &[u32],
    s2: usize,
    n2: usize,
    g: &[u32],
    sg: usize,
    ng: usize,
    out: &[u32],
    zero: &[u32],
) -> bool {
    let mut ok = true;
    let mut e: usize = 0;
    while e < m {
        let j = ej[e] as usize;
        let s = es[e] as usize;
        let io = epo[e] as usize;
        let co = eco[e] as usize;
        if j >= nsrc {
            ok = false;
        } else {
            let lj = lane[j];
            let w1 = wl[lj as usize] as usize;
            if !piv_ok(idx, io, s, lane, lj, nsrc) {
                ok = false;
            }
            if !kimg_ok(z1, s1, w1, j, idx, io, coef, co, s, zero, 0, 0) {
                ok = false;
            }
            if !kimg_ok(z2, s2, n2, j, idx, io, coef, co, s, zero, 0, 0) {
                ok = false;
            }
            if !kimg_ok(g, sg, ng, j, idx, io, coef, co, s, out, e * ng, 1) {
                ok = false;
            }
        }
        e += 1;
    }
    ok
}

/// One row of a product test: for every j < nj,
/// sum_{p<len} a[ao + i*len + p] * b[bo + p*nj + j] == c[co + i*nj + j].
pub fn prod_row_ok(a: &[u32], ao: usize, b: &[u32], bo: usize, c: &[u32], co: usize, i: usize, nj: usize, len: usize) -> bool {
    let mut ok = true;
    let mut j: usize = 0;
    while j < nj {
        if dot(a, ao + i * len, 1, b, bo + j, nj, len) != c[co + i * nj + j] as u64 {
            ok = false;
        }
        j += 1;
    }
    ok
}

/// A (ni x len) * B (len x nj) == C (ni x nj), row-major, at offsets.
pub fn prod_ok(a: &[u32], ao: usize, b: &[u32], bo: usize, c: &[u32], co: usize, ni: usize, nj: usize, len: usize) -> bool {
    let mut ok = true;
    let mut i: usize = 0;
    while i < ni {
        if !prod_row_ok(a, ao, b, bo, c, co, i, nj, len) {
            ok = false;
        }
        i += 1;
    }
    ok
}

/// One row of the identity test: c[co + i*w + j] == [i == j].
pub fn id_row_ok(c: &[u32], co: usize, i: usize, w: usize) -> bool {
    let mut ok = true;
    let mut j: usize = 0;
    while j < w {
        let x = c[co + i * w + j];
        if i == j {
            if x != 1 {
                ok = false;
            }
        } else if x != 0 {
            ok = false;
        }
        j += 1;
    }
    ok
}

/// c[co ..] is the w x w identity.
pub fn id_ok(c: &[u32], co: usize, w: usize) -> bool {
    let mut ok = true;
    let mut i: usize = 0;
    while i < w {
        if !id_row_ok(c, co, i, w) {
            ok = false;
        }
        i += 1;
    }
    ok
}

/// One row of the echelon test: e[a*n + piv[b]] == [a == b] for b < r.
pub fn ech_row_ok(e: &[u32], n: usize, piv: &[u32], a: usize, r: usize) -> bool {
    let mut ok = true;
    let mut b: usize = 0;
    while b < r {
        let x = e[a * n + piv[b] as usize];
        if a == b {
            if x != 1 {
                ok = false;
            }
        } else if x != 0 {
            ok = false;
        }
        b += 1;
    }
    ok
}

/// E is the identity on the pivot columns (EchOK's first clause).
pub fn ech_ok(e: &[u32], n: usize, piv: &[u32], r: usize) -> bool {
    let mut ok = true;
    let mut a: usize = 0;
    while a < r {
        if !ech_row_ok(e, n, piv, a, r) {
            ok = false;
        }
        a += 1;
    }
    ok
}

/// Tags of a column list: l[x] < n and tag[l[x]] == 2x + par.
pub fn tag_list_ok(l: &[u32], len: usize, tag: &[u32], n: usize, par: u32) -> bool {
    let mut ok = true;
    let mut x: usize = 0;
    while x < len {
        let c = l[x] as usize;
        if c >= n {
            ok = false;
        } else if tag[c] as u64 != 2 * (x as u64) + par as u64 {
            ok = false;
        }
        x += 1;
    }
    ok
}

/// Every column is tagged as a pivot or a free column that maps back to it.
pub fn tag_cover_ok(tag: &[u32], n: usize, piv: &[u32], r: usize, fr: &[u32], k: usize) -> bool {
    let mut ok = true;
    let mut c: usize = 0;
    while c < n {
        let t = tag[c] as usize;
        let h = t / 2;
        if t % 2 == 0 {
            if h >= r {
                ok = false;
            } else if piv[h] as usize != c {
                ok = false;
            }
        } else if h >= k {
            ok = false;
        } else if fr[h] as usize != c {
            ok = false;
        }
        c += 1;
    }
    ok
}

/// One row of the n_f test: nm[f*n + t] == [t = fr f] - E[a][fr f] [t = piv a].
pub fn nvec_row_ok(nm: &[u32], e: &[u32], n: usize, fr: &[u32], tag: &[u32], f: usize) -> bool {
    let mut ok = true;
    let mut t: usize = 0;
    let ff = fr[f] as usize;
    while t < n {
        let x = nm[f * n + t] as u64;
        let g = tag[t] as usize;
        let want = if t == ff {
            1
        } else if g % 2 == 0 {
            (P - e[(g / 2) * n + ff] as u64 % P) % P
        } else {
            0
        };
        if x != want {
            ok = false;
        }
        t += 1;
    }
    ok
}

/// The n_f matrix (k x n).
pub fn nvec_ok(nm: &[u32], e: &[u32], n: usize, fr: &[u32], tag: &[u32], k: usize) -> bool {
    let mut ok = true;
    let mut f: usize = 0;
    while f < k {
        if !nvec_row_ok(nm, e, n, fr, tag, f) {
            ok = false;
        }
        f += 1;
    }
    ok
}

/// All lifts: O_l * U_l == I_l and I_l the identity.
pub fn lifts_ok(o: &[u32], u: &[u32], id: &[u32], lw: &[u32], loff: &[u32], nl: usize) -> bool {
    let mut ok = true;
    let mut l: usize = 0;
    while l < nl {
        let w = lw[l] as usize;
        let off = loff[l] as usize;
        if !prod_ok(o, off, u, off, id, off, w, w, w) {
            ok = false;
        }
        if !id_ok(id, off, w) {
            ok = false;
        }
        l += 1;
    }
    ok
}

/// x * y mod P.
pub fn mm(x: u32, y: u32) -> u64 {
    x as u64 * y as u64 % P
}

/// HalfOK: (alpha_9 - 1/2) * h == 1 in QM31 = CM31[u]/(u^2 - (2 + i)), limbs (c0.a, c0.b, c1.a, c1.b).
pub fn half_ok(a: &[u32], h: &[u32]) -> bool {
    // x0 = a0 - 1/2, 1/2 = 2^30 in M31.
    let x0 = ((a[0] as u64 % P) + P - (1u64 << 30)) % P;
    let x0 = x0 as u32;
    let x1 = a[1];
    let x2 = a[2];
    let x3 = a[3];
    let y0 = h[0];
    let y1 = h[1];
    let y2 = h[2];
    let y3 = h[3];
    // p + q i = (x2 + x3 i)(y2 + y3 i)
    let p = (mm(x2, y2) + P - mm(x3, y3)) % P;
    let q = (mm(x2, y3) + mm(x3, y2)) % P;
    // r0 = x0y0 - x1y1 + 2p - q ; r1 = x0y1 + x1y0 + p + 2q
    let r0 = (mm(x0, y0) + P - mm(x1, y1) + 2 * p + P - q) % P;
    let r1 = (mm(x0, y1) + mm(x1, y0) + p + 2 * q) % P;
    // r2 = x0y2 - x1y3 + x2y0 - x3y1 ; r3 = x0y3 + x1y2 + x2y1 + x3y0
    let r2 = (mm(x0, y2) + P - mm(x1, y3) + mm(x2, y0) + P - mm(x3, y1)) % P;
    let r3 = (mm(x0, y3) + mm(x1, y2) + mm(x2, y1) + mm(x3, y0)) % P;
    r0 == 1 && r1 == 0 && r2 == 0 && r3 == 0
}

/// Public column data (the builders' output, a function of the challenges).
pub struct Pub {
    /// Number of opened queries (QueryCard).
    pub nq: u32,
    /// alpha_9 limbs.
    pub a9: Vec<u32>,
    /// Round width (1084) and read-support width (8 (78 + nf)).
    pub rw: u32,
    pub bw: u32,
    /// QPrime referenced sources: lane, own block rows per lane, own columns
    /// (stride os), round columns (stride rw), chain targets (rw x rw).
    pub nsrc: u32,
    pub lane: Vec<u32>,
    pub wl: Vec<u32>,
    pub os: u32,
    pub own: Vec<u32>,
    pub round: Vec<u32>,
    pub tq: Vec<u32>,
    /// relR1 limb functionals (q x bw).
    pub q: u32,
    pub rel: Vec<u32>,
    /// G referenced sources: own (stride gw, gw rows), round (stride rw), bat (stride bw).
    pub ngs: u32,
    pub gw: u32,
    pub glane: Vec<u32>,
    pub gwl: Vec<u32>,
    pub gown: Vec<u32>,
    pub ground: Vec<u32>,
    pub gbat: Vec<u32>,
    /// Lift observation matrices O_l (w_l x w_l at loff[l]).
    pub nl: u32,
    pub lw: Vec<u32>,
    pub loff: Vec<u32>,
    pub lo: Vec<u32>,
}

/// The certificate (all limbs u32; indices u32).
pub struct Cert {
    pub hinv: Vec<u32>,
    /// QPrime kernel entries and their round images rho (m x rw), Y (rw x m).
    pub m: u32,
    pub ej: Vec<u32>,
    pub es: Vec<u32>,
    pub epo: Vec<u32>,
    pub eco: Vec<u32>,
    pub pidx: Vec<u32>,
    pub coef: Vec<u32>,
    pub rho: Vec<u32>,
    pub y: Vec<u32>,
    /// BCondG: U (r x q), E = U Rel (r x bw), pivots, free columns, tags (bw).
    pub r: u32,
    pub k: u32,
    pub u: Vec<u32>,
    pub e: Vec<u32>,
    pub piv: Vec<u32>,
    pub fr: Vec<u32>,
    pub tag: Vec<u32>,
    /// V_G entries, bat images beta (mg x bw), Y_G (k x mg), n_f matrix (k x bw).
    pub mg: u32,
    pub gej: Vec<u32>,
    pub ges: Vec<u32>,
    pub gepo: Vec<u32>,
    pub geco: Vec<u32>,
    pub gpidx: Vec<u32>,
    pub gcoef: Vec<u32>,
    pub beta: Vec<u32>,
    pub yg: Vec<u32>,
    pub nm: Vec<u32>,
    /// Lift right inverses U_l and identities I_l (at loff[l]).
    pub lu: Vec<u32>,
    pub lid: Vec<u32>,
}

/// QPrime_R1: the two-level preimage certificate (PreOK).
pub fn check_qprime(pb: &Pub, c: &Cert) -> bool {
    let rw = pb.rw as usize;
    let m = c.m as usize;
    let zero: [u32; 1] = [0];
    let a = ents_ok(
        &c.ej, &c.es, &c.epo, &c.eco, &c.pidx, &c.coef, m, &pb.lane, &pb.wl, pb.nsrc as usize, &pb.own,
        pb.os as usize, &pb.round, rw, 0, &pb.round, rw, rw, &c.rho, &zero,
    );
    let b = prod_ok(&c.y, 0, &c.rho, 0, &pb.tq, 0, rw, rw, m);
    a && b
}

/// BCondG_R1: E = U Rel in echelon form on a tagged partition (EchOK), and the
/// V_G preimages of the n_f (PreOK2).
pub fn check_bcond(pb: &Pub, c: &Cert) -> bool {
    let n = pb.bw as usize;
    let r = c.r as usize;
    let k = c.k as usize;
    let q = pb.q as usize;
    let mg = c.mg as usize;
    let rw = pb.rw as usize;
    let zero: [u32; 1] = [0];
    let e1 = prod_ok(&c.u, 0, &pb.rel, 0, &c.e, 0, r, n, q);
    let e2 = tag_list_ok(&c.piv, r, &c.tag, n, 0);
    let e3 = tag_list_ok(&c.fr, k, &c.tag, n, 1);
    let e4 = tag_cover_ok(&c.tag, n, &c.piv, r, &c.fr, k);
    let e5 = ech_ok(&c.e, n, &c.piv, r);
    let g1 = ents_ok(
        &c.gej, &c.ges, &c.gepo, &c.geco, &c.gpidx, &c.gcoef, mg, &pb.glane, &pb.gwl, pb.ngs as usize,
        &pb.gown, pb.gw as usize, &pb.ground, rw, rw, &pb.gbat, n, n, &c.beta, &zero,
    );
    let g2 = nvec_ok(&c.nm, &c.e, n, &c.fr, &c.tag, k);
    let g3 = prod_ok(&c.yg, 0, &c.beta, 0, &c.nm, 0, k, n, mg);
    e1 && e2 && e3 && e4 && e5 && g1 && g2 && g3
}

/// The checker.
pub fn check(pb: &Pub, c: &Cert) -> bool {
    let h = half_ok(&pb.a9, &c.hinv);
    let qc = pb.nq <= 22;
    let li = lifts_ok(&pb.lo, &c.lu, &c.lid, &pb.lw, &pb.loff, pb.nl as usize);
    let qp = check_qprime(pb, c);
    let bc = check_bcond(pb, c);
    h && qc && li && qp && bc
}
