//! Research-only sparse reconstruction/transpose in the selected natural tensor basis.
#![allow(dead_code)]
extern crate alloc;
#[path = "../../../../crates/aspis-core/src/circle.rs"]
mod circle;
#[path = "../../../../crates/aspis-core/src/field.rs"]
mod field;
use circle::{secure_ood_circle_point_from_parameter as ood, SecureCirclePoint as Point};
use field::{CM31, M31, QM31 as K};
use std::{hint::black_box, time::Instant};
const D: usize = 512;
const EXT: usize = 514;
fn scalar(n: u32) -> K {
    K::from_cm31(CM31::new(M31(n), M31::ZERO))
}
fn sample(n: u32) -> K {
    K {
        c0: CM31::new(M31(n), M31(n + 1)),
        c1: CM31::new(M31(n + 2), M31(n + 3)),
    }
}
// phi_j(x)=product of T_(2^b)(x) for the set bits of j.
// T_m^2=(1+T_(2m))/2 gives multiplication by x as a carry chain.
fn edges(j: usize) -> Vec<(usize, M31)> {
    let mut row = j;
    let mut bit = 0;
    let mut scale = M31::ONE;
    let mut out = Vec::new();
    while row & (1 << bit) != 0 {
        row ^= 1 << bit;
        scale = scale.mul(field::M31_HALF);
        out.push((row, scale));
        bit += 1;
    }
    out.push((row | (1 << bit), scale));
    out
}
fn xmul(v: &[K]) -> Vec<K> {
    let mut out = vec![K::ZERO; v.len() + 1];
    for (j, v) in v.iter().enumerate() {
        for (r, s) in edges(j) {
            out[r] = out[r].add(v.mul_m31(s));
        }
    }
    out
}
fn xt(v: &[K], input_len: usize) -> Vec<K> {
    (0..input_len)
        .map(|j| {
            edges(j)
                .into_iter()
                .fold(K::ZERO, |a, (r, s)| a.add(v[r].mul_m31(s)))
        })
        .collect()
}
fn dot(a: &[K], b: &[K]) -> K {
    a.iter().zip(b).fold(K::ZERO, |s, (a, b)| s.add(a.mul(*b)))
}
fn phi(j: usize, x: K) -> K {
    let mut r = K::ONE;
    let mut x = x;
    let mut j = j;
    while j != 0 {
        if j & 1 != 0 {
            r = r.mul(x);
        }
        x = x.square().add(x.square()).sub(K::ONE);
        j >>= 1;
    }
    r
}
fn word_eval(q: &[K], p: Point) -> K {
    q.chunks_exact(2).enumerate().fold(K::ZERO, |s, (j, v)| {
        s.add(phi(j, p.x).mul(v[0].add(p.y.mul(v[1]))))
    })
}
fn forward(q: &[K], [a, b, c]: [K; 3]) -> Vec<K> {
    let qa: Vec<K> = q.chunks_exact(2).map(|v| v[0]).collect();
    let qb: Vec<K> = q.chunks_exact(2).map(|v| v[1]).collect();
    let xa = xmul(&qa);
    let xb = xmul(&qb);
    let xxb = xmul(&xb);
    let get = |v: &[K], j: usize| v.get(j).copied().unwrap_or(K::ZERO);
    let mut out = vec![K::ZERO; 2 * EXT];
    for j in 0..EXT {
        out[2 * j] = a
            .mul(get(&qa, j))
            .add(b.mul(get(&xa, j)))
            .add(c.mul(get(&qb, j).sub(get(&xxb, j))));
        out[2 * j + 1] = c
            .mul(get(&qa, j))
            .add(a.mul(get(&qb, j)))
            .add(b.mul(get(&xb, j)));
    }
    out
}
// w has 2*EXT entries: includes arbitrary overflow constraints and ordinary claims.
fn transpose(w: &[K], [a, b, c]: [K; 3]) -> Vec<K> {
    let wa: Vec<K> = w.chunks_exact(2).map(|v| v[0]).collect();
    let wb: Vec<K> = w.chunks_exact(2).map(|v| v[1]).collect();
    let xwa = xt(&wa, D + 1);
    let xxwa = xt(&xwa, D);
    let xwb = xt(&wb, D);
    let mut out = vec![K::ZERO; 2 * D];
    for j in 0..D {
        out[2 * j] = a.mul(wa[j]).add(b.mul(xwa[j])).add(c.mul(wb[j]));
        out[2 * j + 1] = c
            .mul(wa[j].sub(xxwa[j]))
            .add(a.mul(wb[j]))
            .add(b.mul(xwb[j]));
    }
    out
}
fn chord(s: Point, t: Point) -> [K; 3] {
    [s.x.mul(t.y).sub(s.y.mul(t.x)), s.y.sub(t.y), t.x.sub(s.x)]
}
fn main() {
    let p = ood(sample(17)).unwrap();
    let other = ood(sample(41)).unwrap();
    let probe = ood(sample(73)).unwrap();
    // Check x-multiplication identity for every index ever used, independently by evaluation.
    for j in 0..D + 1 {
        for p in [p, other] {
            let rhs = edges(j)
                .into_iter()
                .fold(K::ZERO, |s, (r, w)| s.add(phi(r, p.x).mul_m31(w)));
            assert_eq!(p.x.mul(phi(j, p.x)), rhs);
        }
    }
    let mut checked = 0;
    for l in [
        chord(p, other),
        chord(
            p,
            Point {
                x: p.x,
                y: p.y.neg(),
            },
        ),
    ] {
        let w: Vec<K> = (0..2 * EXT).map(|j| sample(100 + j as u32)).collect();
        let wt = transpose(&w, l);
        for j in 0..2 * D {
            let mut q = vec![K::ZERO; 2 * D];
            q[j] = K::ONE;
            let f = forward(&q, l);
            let mut scale = M31::ONE;
            for _ in 0..9 {
                scale = scale.mul(field::M31_HALF);
            }
            assert_eq!(
                f[1024],
                l[1].mul(q[1022]).sub(l[2].mul(q[1021])).mul_m31(scale)
            );
            assert_eq!(f[1025], l[1].mul(q[1023]).mul_m31(scale));
            assert_eq!(f[1026], l[2].mul(q[1023]).neg().mul_m31(scale));
            assert_eq!(f[1027], K::ZERO);
            assert_eq!(dot(&w, &f), wt[j]);
            assert_eq!(
                word_eval(&f, probe),
                word_eval(&q, probe).mul(l[0].add(l[1].mul(probe.x)).add(l[2].mul(probe.y)))
            );
            checked += 1;
        }
        // Non-image basis elements have a detectable high coefficient.
        for j in [2 * D - 1, 2 * D - 2] {
            let mut q = vec![K::ZERO; 2 * D];
            q[j] = K::ONE;
            assert!(forward(&q, l)[2 * D..].iter().any(|v| *v != K::ZERO));
        }
        // Interior inputs reconstruct inside W; interpolant correction works for arbitrary w.
        let mut q: Vec<K> = (0..2 * D).map(|j| sample(200 + j as u32)).collect();
        q[2 * D - 1] = K::ZERO;
        q[2 * D - 2] = K::ZERO;
        q[2 * D - 3] = K::ZERO;
        let mut f = forward(&q, l);
        assert!(f[2 * D..].iter().all(|v| *v == K::ZERO));
        let i0 = sample(61);
        let ih = sample(67);
        let h = if l[2] != K::ZERO { 2 } else { 1 };
        let correction = w[0].mul(i0).add(w[h].mul(ih));
        f[0] = f[0].add(i0);
        f[h] = f[h].add(ih);
        assert_eq!(dot(&w, &f).sub(correction), dot(&wt, &q));
    }
    println!("PASS {checked} tensor basis reconstruction and transpose identities; 1026 independent x-carry checks");
    println!("PASS malformed top coefficients detected and affine claim correction; no transcript or acceptance claim");
    println!("PASS sparse overflow formulas on all 2048 cases: q[1023]=0 and b*q[1022]-c*q[1021]=0 characterize membership");
    let x_edges: usize = (0..D).map(|j| edges(j).len()).sum();
    let xt_edges: usize = (0..D + 1).map(|j| edges(j).len()).sum::<usize>() + 2 * x_edges;
    println!(
        "transpose kernel: {} QM31 products, {} mixed M31 products; allocations included",
        6 * D,
        xt_edges
    );
    let l = chord(p, other);
    let w: Vec<K> = (0..2 * EXT).map(|j| sample(j as u32)).collect();
    let mut ns = Vec::new();
    for _ in 0..200 {
        let now = Instant::now();
        black_box(transpose(black_box(&w), black_box(l)));
        ns.push(now.elapsed().as_nanos());
    }
    let mean = ns.iter().sum::<u128>() / ns.len() as u128;
    ns.sort();
    println!(
        "host transpose 200 calls: mean {mean} ns, p50 {} ns, p95 {} ns, max {} ns",
        ns[100], ns[189], ns[199]
    );
}
