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
mod grouped_mask;
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
// Product covectors in low-bit-first order; zero factors need no division.
fn tensor(p: &[[K; 2]]) -> Vec<K> {
    (0..1usize << p.len())
        .map(|j| {
            p.iter()
                .enumerate()
                .fold(K::ONE, |v, (k, r)| v.mul(r[(j >> k) & 1]))
        })
        .collect()
}
fn line_dot_x(w: &[[K; 2]], v: &[[K; 2]]) -> (K, K) {
    let n = w.len();
    let mut suffix = vec![K::ONE; n + 1];
    for k in (0..n).rev() {
        suffix[k] = suffix[k + 1].mul(w[k][0].mul(v[k][0]).add(w[k][1].mul(v[k][1])));
    }
    let mut carry = K::ONE;
    let mut total = K::ZERO;
    for k in 0..n {
        let half_down = w[k][0].mul(v[k][1]).half();
        let stop = w[k][1].mul(v[k][0]).add(half_down);
        total = total.add(carry.mul(stop).mul(suffix[k + 1]));
        carry = carry.mul(half_down);
    }
    (suffix[0], total)
}
fn structured_link(w: &[[K; 2]; 10], v: &[[K; 2]; 10], [a, b, c]: [K; 3]) -> K {
    let (d, dx) = line_dot_x(&w[1..], &v[1..]);
    let (_, higher_x) = line_dot_x(&w[2..], &v[2..]);
    let low_dot = w[1][0].mul(v[1][0]).add(w[1][1].mul(v[1][1]));
    // x²=(1+T2)/2; multiplication by T2 starts the carry at bit one.
    let dxx = d.add(low_dot.mul(higher_x)).half();
    let yy = w[0][0].mul(v[0][0]).add(w[0][1].mul(v[0][1]));
    a.mul(d).add(b.mul(dx)).mul(yy).add(
        c.mul(
            d.mul(w[0][1].mul(v[0][0]))
                .add(d.sub(dxx).mul(w[0][0].mul(v[0][1]))),
        ),
    )
}
fn dual_fold_four(mut w: Vec<K>, alpha: [K; 4]) -> [K; 4] {
    for a in alpha {
        let a2 = a.mul(a);
        let a3 = a2.mul(a);
        w = w
            .chunks_exact(4)
            .map(|v| {
                v[0].add(a3.mul(v[1]))
                    .add(a2.mul(v[2]))
                    .add(a.mul(v[3]))
                    .half()
                    .half()
            })
            .collect();
    }
    w.try_into().unwrap()
}
// Direct two-bit contraction. Every m! is one counted generic QM31 product;
// half/add/sub and allocations are separate. Challenge squares are included.
fn block_terminal(w: &[[K; 2]; 10], alpha: [K; 4], [a, b, c]: [K; 3]) -> ([K; 4], usize) {
    let mut count = 0usize;
    macro_rules! m {
        ($x:expr,$y:expr) => {{
            count += 1;
            ($x).mul($y)
        }};
    }
    let powers: [(K, K); 4] = core::array::from_fn(|j| {
        let a2 = m!(alpha[j], alpha[j]);
        (a2, m!(a2, alpha[j]))
    });
    let (a2, a3) = powers[0];
    let ax = alpha[0];
    let [x0, x1] = w[1];
    let [y0, y1] = w[0];
    let i0 = x0.add(m!(a2, x1));
    let c0 = m!(a2, x0).half();
    let s0 = x1.add(c0);
    let i1 = m!(a3, x0).add(m!(ax, x1));
    let c1 = m!(ax, x0).half();
    let s1 = m!(a3, x1).add(c1);
    let y0i1 = m!(y0, i1);
    let u = m!(a, m!(y0, i0).add(m!(y1, i1)))
        .add(m!(b, m!(y0, s0).add(m!(y1, s1))))
        .add(m!(c, m!(y1, i0).add(y0i1.half())));
    let v = m!(b, m!(y0, c0).add(m!(y1, c1))).sub(m!(c, y0i1).half());
    let mut identity = K::ONE;
    let mut ended = K::ZERO;
    let mut carry = K::ONE;
    for round in 1..4 {
        let k = 2 * round;
        let z = [
            m!(w[k][0], w[k + 1][0]),
            m!(w[k][1], w[k + 1][0]),
            m!(w[k][0], w[k + 1][1]),
            m!(w[k][1], w[k + 1][1]),
        ];
        let (a2, a3) = powers[round];
        let ax = alpha[round];
        let same = z[0].add(m!(a3, z[1])).add(m!(a2, z[2])).add(m!(ax, z[3]));
        let stop = z[1]
            .add(m!(a3, z[0].add(z[2])).half())
            .add(m!(a2, z[3]))
            .add(m!(ax, z[2].half().add(z[0].half().half())));
        let next = m!(ax, z[0]).half().half();
        identity = m!(identity, same);
        ended = m!(ended, same).add(m!(carry, stop));
        carry = m!(carry, next);
    }
    let common = m!(u, identity).add(m!(v, ended));
    let active = m!(v, carry);
    let z = [
        m!(w[8][0], w[9][0]),
        m!(w[8][1], w[9][0]),
        m!(w[8][0], w[9][1]),
        m!(w[8][1], w[9][1]),
    ];
    let stop = [
        z[1],
        z[0].add(z[2]).half(),
        z[3],
        z[2].half().add(z[0].half().half()),
    ];
    let out = core::array::from_fn(|j| {
        let mut r = m!(common, z[j]).add(m!(active, stop[j]));
        for _ in 0..8 {
            r = r.half();
        }
        r
    });
    (out, count)
}
fn main() {
    if std::env::args().any(|a| a == "--grouped-test") {
        grouped_mask::run();
        return;
    }
    if std::env::args().any(|a| a == "--cross-fixture") {
        for seed in 0..40u32 {
            let mut tw: [[K; 2]; 10] = core::array::from_fn(|j| {
                [
                    sample(seed + 10 * j as u32),
                    sample(seed + 10 * j as u32 + 1),
                ]
            });
            if seed % 2 == 0 {
                tw[(seed as usize) % 10][0] = K::ZERO;
            }
            let mut alpha = core::array::from_fn(|j| sample(seed + 30 * j as u32 + 1));
            if seed == 0 {
                alpha = [K::ZERO; 4];
            }
            if seed == 1 {
                alpha = [K::ONE; 4];
            }
            if seed == 2 {
                alpha = [K::ONE.neg(), K::ZERO, K::ONE, K::ONE.neg()];
            }
            let mut chord = [sample(seed + 401), sample(seed + 501), sample(seed + 601)];
            if (10..13).contains(&seed) {
                chord[(seed - 10) as usize] = K::ZERO;
            }
            let (values, count) = block_terminal(&tw, alpha, chord);
            let values = values.map(|q| q.mul(sample(seed + 701)));
            let limbs = values.map(|q| [q.c0.a.0, q.c0.b.0, q.c1.a.0, q.c1.b.0]);
            println!(
                "{{\"case\":{seed},\"products_including_outer_scale\":{},\"values\":{limbs:?}}}",
                count + 4
            );
        }
        return;
    }
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
    let mut block_count = 0;
    for seed in 0..40u32 {
        let mut tw: [[K; 2]; 10] = core::array::from_fn(|j| {
            [
                sample(seed + 10 * j as u32),
                sample(seed + 10 * j as u32 + 1),
            ]
        });
        if seed % 2 == 0 {
            tw[(seed as usize) % 10][0] = K::ZERO;
        }
        let mut alpha = core::array::from_fn(|j| sample(seed + 30 * j as u32 + 1));
        if seed == 0 {
            alpha = [K::ZERO; 4];
        }
        if seed == 1 {
            alpha = [K::ONE; 4];
        }
        if seed == 2 {
            alpha = [K::ONE.neg(), K::ZERO, K::ONE, K::ONE.neg()];
        }
        let mut dense_w = tensor(&tw);
        dense_w.resize(2 * EXT, K::ZERO);
        let expected = dual_fold_four(transpose(&dense_w, l), alpha);
        let (actual, n) = block_terminal(&tw, alpha, l);
        assert_eq!(actual, expected);
        block_count = n;
    }
    println!("PASS 40 actual four-fold block cases, all four terminal values, zero factors and degenerate alphas");
    println!("counted block QM31 products={block_count}; independent dense control=3072+1020+8=4100, excludes weight materialization and mixed products");
    for seed in 0..32u32 {
        let mut tw: [[K; 2]; 10] = core::array::from_fn(|j| {
            [
                sample(seed + 10 * j as u32),
                sample(seed + 10 * j as u32 + 1),
            ]
        });
        let mut tv: [[K; 2]; 10] = core::array::from_fn(|j| {
            [
                sample(seed + 20 * j as u32 + 2),
                sample(seed + 20 * j as u32 + 3),
            ]
        });
        if seed % 2 == 0 {
            tw[(seed as usize) % 10][0] = K::ZERO;
            tv[(seed as usize + 3) % 10][1] = K::ZERO;
        }
        let mut dense_w = tensor(&tw);
        dense_w.resize(2 * EXT, K::ZERO);
        assert_eq!(
            structured_link(&tw, &tv, l),
            dot(&dense_w, &forward(&tensor(&tv), l))
        );
    }
    println!("PASS 32 structured rank-one tensor checks including zero factors, against full forward map");
    let tw: [[K; 2]; 10] = core::array::from_fn(|j| [sample(j as u32), sample(j as u32 + 20)]);
    let tv: [[K; 2]; 10] = core::array::from_fn(|j| [sample(j as u32 + 30), sample(j as u32 + 40)]);
    let mut structured_ns = Vec::new();
    for _ in 0..200 {
        let now = Instant::now();
        black_box(structured_link(
            black_box(&tw),
            black_box(&tv),
            black_box(l),
        ));
        structured_ns.push(now.elapsed().as_nanos());
    }
    let mean = structured_ns.iter().sum::<u128>() / 200;
    structured_ns.sort();
    println!(
        "host structured scalar 200 calls: mean {mean} ns, p50 {} ns, p95 {} ns, max {} ns",
        structured_ns[100], structured_ns[189], structured_ns[199]
    );
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
