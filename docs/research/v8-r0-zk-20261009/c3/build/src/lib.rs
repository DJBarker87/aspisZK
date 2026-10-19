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
