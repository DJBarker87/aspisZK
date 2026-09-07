//! Exact full-dimension basis checks; no protocol or security claim.
#![allow(dead_code)]
extern crate alloc;
#[path = "../../../../crates/aspis-core/src/circle.rs"]
mod circle;
#[path = "../../../../crates/aspis-core/src/field.rs"]
mod field;
use circle::{secure_ood_circle_point_from_parameter as ood, SecureCirclePoint as Point};
use field::{CM31, M31, QM31 as K};
const N: usize = 512;
fn scalar(n: u32) -> K {
    K::from_cm31(CM31::new(M31(n), M31::ZERO))
}
fn parameter(n: u32) -> K {
    K {
        c0: CM31::new(M31(n), M31(3)),
        c1: CM31::new(M31(5), M31(7)),
    }
}
fn eval(p: &[K], z: K) -> K {
    p.iter().rev().fold(K::ZERO, |a, b| a.mul(z).add(*b))
}
fn pow(mut x: K, mut n: usize) -> K {
    let mut a = K::ONE;
    while n > 0 {
        if n & 1 == 1 {
            a = a.mul(x)
        }
        x = x.square();
        n >>= 1;
    }
    a
}
fn mul_linear(p: &[K], lo: K, hi: K) -> Vec<K> {
    let mut r = vec![K::ZERO; p.len() + 2];
    for (j, v) in p.iter().enumerate() {
        r[j] = r[j].add(v.mul(lo));
        r[j + 2] = r[j + 2].add(v.mul(hi));
    }
    r
}
fn next_chebyshev(current: &[K], previous: &[K]) -> Vec<K> {
    let mut r = vec![K::ZERO; current.len() + 1];
    for (j, v) in current.iter().enumerate() {
        r[j + 1] = v.add(*v);
    }
    for (j, v) in previous.iter().enumerate() {
        r[j] = r[j].sub(*v);
    }
    r
}
fn check_fold(q: &[K], i: K) {
    let mut a = vec![K::ZERO; N];
    let mut b = vec![K::ZERO; N];
    a[0] = q[N - 1];
    let mut tm = vec![K::ONE];
    let mut t = vec![K::ZERO, K::ONE];
    let mut um = vec![];
    let mut u = vec![K::ONE];
    for j in 1..N {
        let plus = q[N - 1 + j];
        let minus = q[N - 1 - j];
        for (k, v) in t.iter().enumerate() {
            a[k] = a[k].add(v.mul(plus.add(minus)));
        }
        for (k, v) in u.iter().enumerate() {
            b[k] = b[k].add(v.mul(i.mul(plus.sub(minus))));
        }
        let tn = next_chebyshev(&t, &tm);
        tm = t;
        t = tn;
        let un = next_chebyshev(&u, &um);
        um = u;
        u = un;
    }
    assert_eq!(b[N - 1], K::ZERO);
    let alpha = parameter(71);
    let alpha2 = alpha.square();
    let folded: Vec<K> = (0..N / 2)
        .map(|j| {
            a[2 * j]
                .add(alpha.mul(b[2 * j]))
                .add(alpha2.mul(a[2 * j + 1].add(alpha.mul(b[2 * j + 1]))))
        })
        .collect();
    for n in 80..96 {
        let p = ood(parameter(n)).unwrap();
        let z = p.x.add(i.mul(p.y));
        let original = eval(q, z).mul(pow(z, N - 1).try_inv().unwrap());
        assert_eq!(original, eval(&a, p.x).add(p.y.mul(eval(&b, p.x))));
        let value = |x: K, y: K| eval(&a, x).add(y.mul(eval(&b, x)));
        let v = [
            value(p.x, p.y),
            value(p.x, p.y.neg()),
            value(p.x.neg(), p.y.neg()),
            value(p.x.neg(), p.y),
        ];
        // Literal selected nested fold, lifted to K coordinates for this identity test.
        let inv2y = p.y.add(p.y).try_inv().unwrap();
        let inv2x = p.x.add(p.x).try_inv().unwrap();
        let positive = v[0]
            .add(v[1])
            .half()
            .add(alpha.mul(v[0].sub(v[1]).mul(inv2y)));
        let negative = v[2]
            .add(v[3])
            .half()
            .add(alpha.mul(v[2].sub(v[3]).mul(inv2y.neg())));
        let actual = positive
            .add(negative)
            .half()
            .add(alpha2.mul(positive.sub(negative).mul(inv2x)));
        assert_eq!(actual, eval(&folded, p.x.square()));
    }
}
fn main() {
    let i = K::from_cm31(CM31::new(M31::ZERO, M31::ONE));
    assert_eq!(i.square(), K::ONE.neg());
    let half = scalar(2).try_inv().unwrap();
    let inv2i = i.neg().mul(half);
    let p0 = ood(parameter(11)).unwrap();
    let pairs = [
        [p0, ood(parameter(29)).unwrap()],
        [
            p0,
            Point {
                x: p0.x,
                y: p0.y.neg(),
            },
        ],
    ];
    let mut cases = 0;
    for points in pairs {
        let [s, t] = points;
        let a = s.x.mul(t.y).sub(s.y.mul(t.x));
        let b = s.y.sub(t.y);
        let c = t.x.sub(s.x);
        // L(z) = lo/z + a + hi*z; z=x+i*y.
        let lo = b.mul(half).sub(c.mul(inv2i));
        let hi = b.mul(half).add(c.mul(inv2i));
        assert_ne!(lo, K::ZERO);
        assert_ne!(hi, K::ZERO);
        let z0 = s.x.add(i.mul(s.y));
        let z1 = t.x.add(i.mul(t.y));
        assert_eq!(eval(&[lo, a, hi], z0), K::ZERO);
        assert_eq!(eval(&[lo, a, hi], z1), K::ZERO);
        let use_x = s.x != t.x;
        let h0 = if use_x { s.x } else { s.y };
        let h1 = if use_x { t.x } else { t.y };
        let inv = h0.sub(h1).try_inv().unwrap();
        let invhi = hi.try_inv().unwrap();
        let mut xpower = vec![K::ONE];
        for k in 0..N {
            for with_y in [false, true] {
                let f = if with_y {
                    mul_linear(&xpower, inv2i.neg(), inv2i)
                } else {
                    xpower.clone()
                };
                let degree = k + usize::from(with_y);
                let v0 = eval(&f, z0).mul(pow(z0, degree).try_inv().unwrap());
                let v1 = eval(&f, z1).mul(pow(z1, degree).try_inv().unwrap());
                let slope = v0.sub(v1).mul(inv);
                let intercept = v0.sub(slope.mul(h0));
                let (il, ih) = if use_x {
                    (slope.mul(half), slope.mul(half))
                } else {
                    (slope.mul(inv2i).neg(), slope.mul(inv2i))
                };
                let mut rem = vec![K::ZERO; 2 * N + 1];
                rem[N - degree..N - degree + f.len()].copy_from_slice(&f);
                rem[N] = rem[N].sub(intercept);
                rem[N - 1] = rem[N - 1].sub(il);
                rem[N + 1] = rem[N + 1].sub(ih);
                let numerator = rem.clone();
                let mut q = vec![K::ZERO; 2 * N - 1];
                for j in (2..rem.len()).rev() {
                    let v = rem[j].mul(invhi);
                    q[j - 2] = v;
                    rem[j] = K::ZERO;
                    rem[j - 1] = rem[j - 1].sub(v.mul(a));
                    rem[j - 2] = rem[j - 2].sub(v.mul(lo));
                }
                assert!(rem.iter().all(|v| *v == K::ZERO));
                // q is z^(N-1)*Q. Exact convolution proves equality everywhere.
                let mut rebuilt = vec![K::ZERO; 2 * N + 1];
                for (j, v) in q.iter().enumerate() {
                    for (d, l) in [lo, a, hi].iter().enumerate() {
                        rebuilt[j + d] = rebuilt[j + d].add(v.mul(*l));
                    }
                }
                assert_eq!(rebuilt, numerator);
                // Original space lacks x^512: its extreme Laurent coefficients sum to zero.
                assert_eq!(hi.mul(q[2 * N - 2]).add(lo.mul(q[0])), K::ZERO);
                if k == N - 1 && with_y {
                    check_fold(&q, i);
                }
                cases += 1;
            }
            xpower = mul_linear(&xpower, half, half);
        }
        // A generic low-degree Q is NOT enough: z^511 yields a forbidden x^512 term.
        assert_ne!(hi, K::ZERO);
    }
    println!("PASS {cases} exact basis quotients (1024 basis vectors, two legal OOD pairs)");
    println!("PASS zero remainders, coefficientwise reconstruction, Laurent support [-511,511], top constraint");
    println!("Includes equal-x/opposite-y branch; generic quotient-to-original membership needs an extra constraint");
    println!("PASS two degree-512 input quotients: Chebyshev reconstruction and 32 nested-fold checks against degree-255 polynomials");
}
