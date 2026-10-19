//! Extraction-friendly copies of the P_R1 checker's column builders (D57.3, D53.2).
//!
//! Same rules as c3/check: no_std + alloc, monomorphic, u32 limbs / u64
//! intermediates with checked arithmetic, plain `while` loops, one loop per
//! function, branch-free bodies (selections are bool-to-integer products).
//! QM31 values are `[u32; 4]` limbs (c0.a, c0.b, c1.a, c1.b) of
//! QM31 = CM31[u]/(u^2 - (2 + i)), CM31 = M31[i]/(i^2 + 1).
//!
//! Builder 1 (this file): the ChainT0K4 targets (z9c.rs `chain_targets`, i.e.
//! probe.rs `normalize_d(unflat e_i, final_value(unflat e_i))` flattened).  The
//! unit vector `unflat e_i` (i = 4p + k) is read on the fly (`vget`), and
//! `final_value` is probe.rs `last_coeff` + Horner at alpha_9 with each round
//! evaluated as `((H·α + co1)·α + co0)`, H the Horner sum of co[2..28].  The
//! inverse of alpha_9 - 1/2 is the certificate's `hinv` (checked by HalfOK).
#![no_std]
extern crate alloc;
use alloc::vec::Vec;

pub const P: u64 = 0x7fff_ffff;

pub fn fadd(x: u32, y: u32) -> u32 {
    ((x as u64 + y as u64) % P) as u32
}
pub fn fsub(x: u32, y: u32) -> u32 {
    ((x as u64 % P + P - y as u64 % P) % P) as u32
}
pub fn fmul(x: u32, y: u32) -> u32 {
    ((x as u64 * y as u64) % P) as u32
}
pub fn qadd(x: [u32; 4], y: [u32; 4]) -> [u32; 4] {
    [fadd(x[0], y[0]), fadd(x[1], y[1]), fadd(x[2], y[2]), fadd(x[3], y[3])]
}
pub fn qsub(x: [u32; 4], y: [u32; 4]) -> [u32; 4] {
    [fsub(x[0], y[0]), fsub(x[1], y[1]), fsub(x[2], y[2]), fsub(x[3], y[3])]
}
/// QM31 product (probe field.rs Karatsuba, schoolbook form).
pub fn qmul(x: [u32; 4], y: [u32; 4]) -> [u32; 4] {
    let p = fsub(fmul(x[2], y[2]), fmul(x[3], y[3]));
    let q = fadd(fmul(x[2], y[3]), fmul(x[3], y[2]));
    let r0 = fsub(fadd(fsub(fmul(x[0], y[0]), fmul(x[1], y[1])), fadd(p, p)), q);
    let r1 = fadd(fadd(fadd(fmul(x[0], y[1]), fmul(x[1], y[0])), p), fadd(q, q));
    let r2 = fsub(fadd(fsub(fmul(x[0], y[2]), fmul(x[1], y[3])), fmul(x[2], y[0])), fmul(x[3], y[1]));
    let r3 = fadd(fadd(fadd(fmul(x[0], y[3]), fmul(x[1], y[2])), fmul(x[2], y[1])), fmul(x[3], y[0]));
    [r0, r1, r2, r3]
}
/// Coordinate q of the unit vector unflat(e_{4p+k}): tower element k at q = p.
pub fn vget(p: usize, k: usize, q: usize) -> [u32; 4] {
    let s = q == p;
    [(s & (k == 0)) as u32, (s & (k == 1)) as u32, (s & (k == 2)) as u32, (s & (k == 3)) as u32]
}
/// sum_{t=1}^{26} v[1 + 27j + t].
pub fn rsum(p: usize, k: usize, j: usize) -> [u32; 4] {
    let mut acc: [u32; 4] = [0, 0, 0, 0];
    let mut t: usize = 1;
    while t < 27 {
        acc = qadd(acc, vget(p, k, 1 + 27 * j + t));
        t += 1;
    }
    acc
}
/// H = sum_{d=2}^{27} v[1 + 27j + d - 1] a^{d-2} (Horner from d = 27 down).
pub fn rhorner(p: usize, k: usize, j: usize, a: [u32; 4]) -> [u32; 4] {
    let mut acc: [u32; 4] = [0, 0, 0, 0];
    let mut t: usize = 0;
    while t < 26 {
        acc = qadd(qmul(acc, a), vget(p, k, 1 + 27 * j + 26 - t));
        t += 1;
    }
    acc
}
/// Round j of last_coeff evaluated at a: co0 = v[1+27j], co1 = prev - 2 co0 - sum, value = pev(co, a).
pub fn round(p: usize, k: usize, j: usize, prev: [u32; 4], a: [u32; 4]) -> [u32; 4] {
    let co0 = vget(p, k, 1 + 27 * j);
    let s = rsum(p, k, j);
    let co1 = qsub(qsub(prev, qadd(co0, co0)), s);
    let h = rhorner(p, k, j, a);
    qadd(qmul(qadd(qmul(h, a), co1), a), co0)
}
/// final_value(unflat e_{4p+k}, alpha), alpha limbs al[4j..4j+4].
pub fn final_value(p: usize, k: usize, al: &[u32]) -> [u32; 4] {
    let mut prev = vget(p, k, 0);
    let mut j: usize = 0;
    while j < 10 {
        let a = [al[4 * j], al[4 * j + 1], al[4 * j + 2], al[4 * j + 3]];
        prev = round(p, k, j, prev, a);
        j += 1;
    }
    prev
}
/// normalize_d's coordinate-244 correction for unit i: final_value * hinv * 1/2.
pub fn corr(i: usize, al: &[u32], hinv: &[u32]) -> [u32; 4] {
    let h = [hinv[0], hinv[1], hinv[2], hinv[3]];
    let half: [u32; 4] = [1_073_741_824, 0, 0, 0];
    qmul(qmul(final_value(i / 4, i % 4, al), h), half)
}
/// Row i of the chain targets: e_i + corr_i on the four limbs of coordinate 244.
pub fn fill_row(out: Vec<u32>, i: usize, c: [u32; 4]) -> Vec<u32> {
    let mut out = out;
    let mut t: usize = 0;
    while t < 1084 {
        let on = (t / 4 == 244) as u32;
        out.push(fadd((t == i) as u32, fmul(on, c[t % 4])));
        t += 1;
    }
    out
}
/// The 1084 x 1084 ChainT0K4 target matrix, row-major (the checker's `tq`).
pub fn fill_tq(al: &[u32], hinv: &[u32]) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < 1084 {
        let c = corr(i, al, hinv);
        out = fill_row(out, i, c);
        i += 1;
    }
    out
}

// ------------------------------------------------------------------------------
// Builder 2 (D59.2): the lift observation columns (pb.lo), z9c.rs `lift_src` on
// probe.rs `raw_c` rows.  Inputs taken as arrays under named premises (D59.2
// ruling): the transport table `tr` (= pi), the OOD points `zz` (8 limbs each:
// x then y), the stored points `sx`, `sy` of the opened (query, slot) pairs in
// list order, and the copy-inactive flags `inact` (0/1 per row).
// ------------------------------------------------------------------------------

pub const P2: [usize; 10] = [512, 256, 128, 64, 32, 16, 8, 4, 2, 1];

pub fn qone() -> [u32; 4] {
    [1, 0, 0, 0]
}
pub fn qbase(v: u32) -> [u32; 4] {
    [v, 0, 0, 0]
}
pub fn aget(al: &[u32], j: usize) -> [u32; 4] {
    [al[4 * j], al[4 * j + 1], al[4 * j + 2], al[4 * j + 3]]
}
/// succCarry: prod_{k < n} a_{9-k} (accumulated as a_{9-k} * acc).
pub fn scarry(al: &[u32], n: usize) -> [u32; 4] {
    let mut acc = qone();
    let mut k: usize = 0;
    while k < n {
        acc = qmul(aget(al, 9 - k), acc);
        k += 1;
    }
    acc
}
/// Coordinate c of opening point g (0: alpha, 1: successor point, 2: xor-12 point).
pub fn point_coord(al: &[u32], g: usize, c: usize) -> [u32; 4] {
    if g == 0 {
        aget(al, c)
    } else if g == 1 {
        let p = aget(al, c);
        let cr = scarry(al, 9 - c);
        qsub(qadd(p, cr), qadd(qmul(p, cr), qmul(p, cr)))
    } else if c == 7 || c == 6 {
        qsub(qone(), aget(al, c))
    } else {
        aget(al, c)
    }
}
/// eq(point g, r) = prod_i (bit_i(r) ? p_i : 1 - p_i), bit i = r / 2^(9-i) mod 2.
pub fn eqw(al: &[u32], g: usize, r: usize) -> [u32; 4] {
    let mut acc = qone();
    let mut i: usize = 0;
    while i < 10 {
        let bit = ((r / P2[i]) % 2) as u32;
        let p = point_coord(al, g, i);
        let f = qadd(qsub(qone(), p), qmul(qbase(bit), qsub(qadd(p, p), qone())));
        acc = qmul(acc, f);
        i += 1;
    }
    acc
}
pub fn qpow(x: [u32; 4], e: usize) -> [u32; 4] {
    let mut acc = qone();
    let mut t: usize = 0;
    while t < e {
        acc = qmul(acc, x);
        t += 1;
    }
    acc
}
/// h_weight(alpha, co).
pub fn hw(al: &[u32], co: usize) -> [u32; 4] {
    if co < 28 {
        qpow(aget(al, 8), co)
    } else if co < 56 {
        qpow(aget(al, 9), co - 28)
    } else {
        [0, 0, 0, 0]
    }
}
/// natural(n, x) = prod over the bits b of n of D_b(x), D_0 = x, D_{b+1} = 2 D_b^2 - 1 (10 bits).
pub fn nat_loop(out: [u32; 4], f: [u32; 4], m: usize, b: usize) -> [u32; 4] {
    let mut out = out;
    let mut f = f;
    let mut m = m;
    let mut b = b;
    while b < 10 {
        let bit = (m % 2) as u32;
        out = qmul(out, qadd(qone(), qmul(qbase(bit), qsub(f, qone()))));
        f = qsub(qadd(qmul(f, f), qmul(f, f)), qone());
        m = m / 2;
        b += 1;
    }
    out
}
pub fn nat_q(n: usize, x: [u32; 4]) -> [u32; 4] {
    nat_loop(qone(), x, n, 0)
}
/// evalrow(co, (x, y)) = natural(co / 2, x) * (co odd ? y : 1).
pub fn evq(co: usize, x: [u32; 4], y: [u32; 4]) -> [u32; 4] {
    let v = nat_q(co / 2, x);
    if co % 2 == 0 {
        v
    } else {
        qmul(v, y)
    }
}
/// The 6 head QM31 values of row r: claims g = 0..2, extra g = 3, OOD g = 4, 5.
pub fn head_q(al: &[u32], zz: &[u32], tr: &[u32], r: usize, g: usize) -> [u32; 4] {
    let co = tr[r] as usize;
    if g < 3 {
        eqw(al, g, r)
    } else if g == 3 {
        hw(al, co)
    } else {
        evq(co, aget(zz, 2 * (g - 4)), aget(zz, 2 * (g - 4) + 1))
    }
}
/// C1 raw coordinate i of row r: head limbs, then the base opened evaluations.
pub fn c1_val(al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], r: usize, i: usize) -> u32 {
    if i < 24 {
        let q = head_q(al, zz, tr, r, i / 4);
        q[i % 4]
    } else {
        let v = evq(tr[r] as usize, qbase(sx[i - 24]), qbase(sy[i - 24]));
        v[0]
    }
}
/// C1 lift column entry (balanced at 1023).
pub fn c1_entry(al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], inact: &[u32], r: usize, i: usize) -> u32 {
    fsub(c1_val(al, zz, tr, sx, sy, r, i), fmul(inact[r], c1_val(al, zz, tr, sx, sy, 1023, i)))
}
/// tower(k).
pub fn tbq(k: usize) -> [u32; 4] {
    [(k == 0) as u32, (k == 1) as u32, (k == 2) as u32, (k == 3) as u32]
}
/// H1 raw coordinate i of (row r, tower limb k): tower(k) times the row's values.
pub fn h1_val(al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], r: usize, k: usize, i: usize) -> u32 {
    if i < 24 {
        let q = qmul(tbq(k), head_q(al, zz, tr, r, i / 4));
        q[i % 4]
    } else {
        let m = i - 24;
        let o = 4 * (m / 16) + (m % 16) / 4;
        let v = evq(tr[r] as usize, qbase(sx[o]), qbase(sy[o]));
        let q = qmul(tbq(k), v);
        q[m % 4]
    }
}
/// H1 lift column entry (balanced at 0).
pub fn h1_entry(al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], inact: &[u32], r: usize, k: usize, i: usize) -> u32 {
    fsub(h1_val(al, zz, tr, sx, sy, r, k, i), fmul(inact[r], h1_val(al, zz, tr, sx, sy, 0, k, i)))
}
/// One row i of C1 lift l: entries for the selected rows sel1[l*w + x].
pub fn c1_row(out: Vec<u32>, al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], inact: &[u32], sel1: &[u32], l: usize, w: usize, i: usize) -> Vec<u32> {
    let mut out = out;
    let mut x: usize = 0;
    while x < w {
        out.push(c1_entry(al, zz, tr, sx, sy, inact, sel1[l * w + x] as usize, i));
        x += 1;
    }
    out
}
pub fn c1_lift(out: Vec<u32>, al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], inact: &[u32], sel1: &[u32], l: usize, w: usize) -> Vec<u32> {
    let mut out = out;
    let mut i: usize = 0;
    while i < w {
        out = c1_row(out, al, zz, tr, sx, sy, inact, sel1, l, w, i);
        i += 1;
    }
    out
}
pub fn c1_lifts(out: Vec<u32>, al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], inact: &[u32], sel1: &[u32], w: usize) -> Vec<u32> {
    let mut out = out;
    let mut l: usize = 0;
    while l < 16 {
        out = c1_lift(out, al, zz, tr, sx, sy, inact, sel1, l, w);
        l += 1;
    }
    out
}
/// One row i of the H1 lift: entries for the selected (row, limb) pairs selh[x] = 4 r + k.
pub fn h1_row(out: Vec<u32>, al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], inact: &[u32], selh: &[u32], w: usize, i: usize) -> Vec<u32> {
    let mut out = out;
    let mut x: usize = 0;
    while x < w {
        let e = selh[x] as usize;
        out.push(h1_entry(al, zz, tr, sx, sy, inact, e / 4, e % 4, i));
        x += 1;
    }
    out
}
pub fn h1_lift(out: Vec<u32>, al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], inact: &[u32], selh: &[u32], w: usize) -> Vec<u32> {
    let mut out = out;
    let mut i: usize = 0;
    while i < w {
        out = h1_row(out, al, zz, tr, sx, sy, inact, selh, w, i);
        i += 1;
    }
    out
}
/// The checker's lift observation matrices pb.lo: 16 C1 lifts (w1 = 24 + 4 nq) then the H1 lift
/// (wh = 24 + 16 nq), each row-major (row i = coordinate, column x = selected source).
pub fn fill_lo(al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], inact: &[u32], sel1: &[u32], selh: &[u32], nq: usize) -> Vec<u32> {
    let out: Vec<u32> = Vec::new();
    let out = c1_lifts(out, al, zz, tr, sx, sy, inact, sel1, 24 + 4 * nq);
    h1_lift(out, al, zz, tr, sx, sy, inact, selh, 24 + 16 * nq)
}

// ------------------------------------------------------------------------------
// Builder 3 (D62): the own columns of the referenced sources (pb.own, pb.gown),
// z9.rs `Lanes::raw/bal` on the same raw_c rows as the lifts, balanced at row 0.
// Source t has kind kind[t] (0..9 mask-only lane, 10 = G, 11 = D), row srow[t]
// (>= 1) and tower limb slimb[t]; its column is padded to os limbs.
// ------------------------------------------------------------------------------

/// Mask-only own entry: raw C1 coordinate i of row r, balanced at row 0.
pub fn own_c1(al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], inact: &[u32], r: usize, i: usize) -> u32 {
    fsub(c1_val(al, zz, tr, sx, sy, r, i), fmul(inact[r], c1_val(al, zz, tr, sx, sy, 0, i)))
}
/// Own entry i of a source (0 beyond the lane's block width).
pub fn own_val(al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], inact: &[u32], kind: usize, r: usize, k: usize, i: usize, wb: usize, we: usize) -> u32 {
    if kind < 10 {
        if i < wb {
            own_c1(al, zz, tr, sx, sy, inact, r, i)
        } else {
            0
        }
    } else if i < we {
        h1_entry(al, zz, tr, sx, sy, inact, r, k, i)
    } else {
        0
    }
}
pub fn own_col(out: Vec<u32>, al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], inact: &[u32], kind: usize, r: usize, k: usize, os: usize, wb: usize, we: usize) -> Vec<u32> {
    let mut out = out;
    let mut i: usize = 0;
    while i < os {
        out.push(own_val(al, zz, tr, sx, sy, inact, kind, r, k, i, wb, we));
        i += 1;
    }
    out
}
/// The own matrix of n referenced sources (column t at t*os).
pub fn fill_own(al: &[u32], zz: &[u32], tr: &[u32], sx: &[u32], sy: &[u32], inact: &[u32], kind: &[u32], srow: &[u32], slimb: &[u32], n: usize, os: usize, nq: usize) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        out = own_col(out, al, zz, tr, sx, sy, inact, kind[t] as usize, srow[t] as usize, slimb[t] as usize, os, 24 + 4 * nq, 24 + 16 * nq);
        t += 1;
    }
    out
}

// ------------------------------------------------------------------------------
// Builder 4 (D64 hRel): the relR1 limb functionals pb.rel (z9b.rs `design_relations`
// with line reading 1, z9.rs `Rel::limb_functionals`, BAT0 dropped).  WideExact
// W = QM31[v]/(v^2 - u), u = (0, 0, 1, 0), limbs (lo QM31, hi QM31).  Lean cells:
// 0..7 round0, 7..14 round1, 14..14+nf folded (positions fpos), 14+nf.. final.
// Relation rho has kind rk[rho] (0 s2a, 1 s2b, 2 s1, 3 circ at query ru[rho],
// 4 line at the parent ru[rho] / 4 of query ru[rho]); the line inverses
// li[3 rho + s] and the stored log-16 node x16[rho] are inputs.  ti is the
// inverse transport (ti[j] = pi^{-1}(j)); op holds the four openings (8 limbs each).
// ------------------------------------------------------------------------------

pub fn wlo(x: [u32; 8]) -> [u32; 4] {
    [x[0], x[1], x[2], x[3]]
}
pub fn whi(x: [u32; 8]) -> [u32; 4] {
    [x[4], x[5], x[6], x[7]]
}
pub fn wmk(a: [u32; 4], b: [u32; 4]) -> [u32; 8] {
    [a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]]
}
pub fn wadd(x: [u32; 8], y: [u32; 8]) -> [u32; 8] {
    wmk(qadd(wlo(x), wlo(y)), qadd(whi(x), whi(y)))
}
pub fn wsub(x: [u32; 8], y: [u32; 8]) -> [u32; 8] {
    wmk(qsub(wlo(x), wlo(y)), qsub(whi(x), whi(y)))
}
/// (a + b v)(c + d v) = (ac + u bd) + (ad + bc) v.
pub fn wmul(x: [u32; 8], y: [u32; 8]) -> [u32; 8] {
    let a = wlo(x);
    let b = whi(x);
    let c = wlo(y);
    let d = whi(y);
    wmk(qadd(qmul(a, c), qmul([0, 0, 1, 0], qmul(b, d))), qadd(qmul(a, d), qmul(b, c)))
}
pub fn wq(a: [u32; 4]) -> [u32; 8] {
    wmk(a, [0, 0, 0, 0])
}
pub fn wbase(v: u32) -> [u32; 8] {
    wq(qbase(v))
}
pub fn wzero() -> [u32; 8] {
    wq([0, 0, 0, 0])
}
/// WideExact basis element m (limb m = 1).
pub fn wunit(m: usize) -> [u32; 8] {
    [(m == 0) as u32, (m == 1) as u32, (m == 2) as u32, (m == 3) as u32, (m == 4) as u32, (m == 5) as u32, (m == 6) as u32, (m == 7) as u32]
}
pub fn wget(op: &[u32], i: usize) -> [u32; 8] {
    [op[8 * i], op[8 * i + 1], op[8 * i + 2], op[8 * i + 3], op[8 * i + 4], op[8 * i + 5], op[8 * i + 6], op[8 * i + 7]]
}
pub fn wpow(x: [u32; 8], e: usize) -> [u32; 8] {
    let mut acc = wq(qone());
    let mut t: usize = 0;
    while t < e {
        acc = wmul(acc, x);
        t += 1;
    }
    acc
}
/// ell_k(e_j) at row r = pi^{-1}(j): k = 0 the inactive flag, k = 1..6 the head value k - 1.
pub fn ellq(al: &[u32], zz: &[u32], tr: &[u32], inact: &[u32], r: usize, k: usize) -> [u32; 4] {
    if k == 0 {
        qbase(inact[r])
    } else {
        head_q(al, zz, tr, r, k - 1)
    }
}
pub fn wt_loop(acc: [u32; 8], al: &[u32], zz: &[u32], tr: &[u32], inact: &[u32], op: &[u32], r: usize, k: usize) -> [u32; 8] {
    let mut acc = acc;
    let mut k = k;
    while k < 7 {
        acc = wadd(acc, wmul(wpow(wget(op, 1), k), wq(ellq(al, zz, tr, inact, r, k))));
        k += 1;
    }
    acc
}
/// weightsR1 j = sum_{k < 7} kappa^k ell_k(e_j), kappa = opening 1.
pub fn wt(al: &[u32], zz: &[u32], tr: &[u32], inact: &[u32], ti: &[u32], op: &[u32], j: usize) -> [u32; 8] {
    wt_loop(wzero(), al, zz, tr, inact, op, ti[j] as usize, 0)
}
pub fn df1_loop(acc: [u32; 8], al: &[u32], zz: &[u32], tr: &[u32], inact: &[u32], ti: &[u32], op: &[u32], d: usize, t: usize) -> [u32; 8] {
    let mut acc = acc;
    let mut t = t;
    while t < 4 {
        acc = wadd(acc, wmul(wt(al, zz, tr, inact, ti, op, 4 * d + t), wpow(wget(op, 2), (4 - t) % 4)));
        t += 1;
    }
    acc
}
/// w1 d = quarter * sum_t weightsR1(4 d + t) alpha0^((4 - t) % 4), alpha0 = opening 2.
pub fn df1(al: &[u32], zz: &[u32], tr: &[u32], inact: &[u32], ti: &[u32], op: &[u32], d: usize) -> [u32; 8] {
    wmul(wbase(536870912), df1_loop(wzero(), al, zz, tr, inact, ti, op, d, 0))
}
pub fn df2_loop(acc: [u32; 8], al: &[u32], zz: &[u32], tr: &[u32], inact: &[u32], ti: &[u32], op: &[u32], e: usize, t: usize) -> [u32; 8] {
    let mut acc = acc;
    let mut t = t;
    while t < 4 {
        acc = wadd(acc, wmul(df1(al, zz, tr, inact, ti, op, 4 * e + t), wpow(wget(op, 3), (4 - t) % 4)));
        t += 1;
    }
    acc
}
/// w2 e = quarter * sum_t w1(4 e + t) alpha1^((4 - t) % 4), alpha1 = opening 3.
pub fn df2(al: &[u32], zz: &[u32], tr: &[u32], inact: &[u32], ti: &[u32], op: &[u32], e: usize) -> [u32; 8] {
    wmul(wbase(536870912), df2_loop(wzero(), al, zz, tr, inact, ti, op, e, 0))
}
/// pairFoldValue: (l + r) / 2 + c ((l - r) inv).
pub fn pfold(c: [u32; 8], inv: [u32; 8], l: [u32; 8], r: [u32; 8]) -> [u32; 8] {
    wadd(wmul(wadd(l, r), wbase(1073741824)), wmul(c, wmul(wsub(l, r), inv)))
}
/// lineFoldValue(a, inv0, inv1, inv2, unit_t).
pub fn lfv(a: [u32; 8], i0: [u32; 8], i1: [u32; 8], i2: [u32; 8], t: usize) -> [u32; 8] {
    pfold(wmul(a, a), i2, pfold(a, i0, wbase((t == 0) as u32), wbase((t == 1) as u32)), pfold(a, i1, wbase((t == 2) as u32), wbase((t == 3) as u32)))
}
/// Coefficient of the line relation rho at the folded position p.
pub fn line_fold(op: &[u32], ru: &[u32], li: &[u32], rho: usize, p: usize) -> [u32; 8] {
    let v = ru[rho] as usize / 4;
    wmul(wbase((p / 4 == v) as u32), lfv(wget(op, 3), wbase(li[3 * rho]), wbase(li[3 * rho + 1]), wbase(li[3 * rho + 2]), p % 4))
}
/// Coefficient of relation rho at Lean cell i.
pub fn coef(al: &[u32], zz: &[u32], tr: &[u32], inact: &[u32], ti: &[u32], op: &[u32], fpos: &[u32], rk: &[u32], ru: &[u32], li: &[u32], x16: &[u32], nf: usize, rho: usize, i: usize) -> [u32; 8] {
    let kind = rk[rho];
    if kind == 0 {
        wbase((i == 0) as u32 + (i == 4) as u32)
    } else if kind == 1 {
        if i < 7 {
            wsub(wzero(), wmul(wbase(536870912), wpow(wget(op, 2), i)))
        } else {
            wbase(((i == 7) | (i == 11)) as u32)
        }
    } else if kind == 2 {
        if i < 7 {
            wzero()
        } else if i < 14 {
            wpow(wget(op, 3), i - 7)
        } else if i < 14 + nf {
            wzero()
        } else {
            wsub(wzero(), df2(al, zz, tr, inact, ti, op, i - (14 + nf)))
        }
    } else if kind == 3 {
        if i < 14 {
            wzero()
        } else if i < 14 + nf {
            wbase((fpos[i - 14] == ru[rho]) as u32)
        } else {
            wzero()
        }
    } else if i < 14 {
        wzero()
    } else if i < 14 + nf {
        line_fold(op, ru, li, rho, fpos[i - 14] as usize)
    } else {
        wsub(wzero(), wq(nat_q(i - (14 + nf), qbase(x16[rho]))))
    }
}
/// Entry (8 rho + k, 8 i + m): limb k of coef(rho, i) * unit(m).
pub fn rel_entry(al: &[u32], zz: &[u32], tr: &[u32], inact: &[u32], ti: &[u32], op: &[u32], fpos: &[u32], rk: &[u32], ru: &[u32], li: &[u32], x16: &[u32], nf: usize, x: usize, c: usize) -> u32 {
    let z = wmul(coef(al, zz, tr, inact, ti, op, fpos, rk, ru, li, x16, nf, x / 8, c / 8), wunit(c % 8));
    z[x % 8]
}
pub fn rel_row(out: Vec<u32>, al: &[u32], zz: &[u32], tr: &[u32], inact: &[u32], ti: &[u32], op: &[u32], fpos: &[u32], rk: &[u32], ru: &[u32], li: &[u32], x16: &[u32], nf: usize, x: usize) -> Vec<u32> {
    let mut out = out;
    let mut c: usize = 0;
    while c < 8 * (78 + nf) {
        out.push(rel_entry(al, zz, tr, inact, ti, op, fpos, rk, ru, li, x16, nf, x, c));
        c += 1;
    }
    out
}
/// The checker's relation matrix pb.rel: q = 8 nr rows, bw = 8 (78 + nf) columns, row-major.
pub fn fill_rel(al: &[u32], zz: &[u32], tr: &[u32], inact: &[u32], ti: &[u32], op: &[u32], fpos: &[u32], rk: &[u32], ru: &[u32], li: &[u32], x16: &[u32], nf: usize, q: usize) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::new();
    let mut x: usize = 0;
    while x < q {
        out = rel_row(out, al, zz, tr, inact, ti, op, fpos, rk, ru, li, x16, nf, x);
        x += 1;
    }
    out
}
