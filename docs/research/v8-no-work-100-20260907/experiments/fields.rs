//! Standalone optimized microbench; includes the pinned production QM31 kernel.
#![allow(dead_code)]
#[path = "../../../../crates/aspis-core/src/field.rs"]
mod field;
use field::{CM31, M31, P, QM31};
use std::{hint::black_box, time::Instant};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Q5([M31; 5]);
impl Q5 {
    const ONE: Self = Self([M31(1), M31(0), M31(0), M31(0), M31(0)]);
    const X: Self = Self([M31(0), M31(1), M31(0), M31(0), M31(0)]);
    fn mul(self, b: Self) -> Self {
        let mut c = [M31(0); 9];
        for i in 0..5 {
            for j in 0..5 {
                c[i + j] = c[i + j].add(self.0[i].mul(b.0[j]));
            }
        }
        for i in (5..9).rev() {
            c[i - 5] = c[i - 5].add(c[i].mul(M31(6)));
            c[i - 4] = c[i - 4].add(c[i]);
        }
        Self(c[..5].try_into().unwrap())
    }
    fn mixed(self, b: M31) -> Self {
        Self(self.0.map(|x| x.mul(b)))
    }
    fn pow(self, mut e: u32) -> Self {
        let mut a = self;
        let mut r = Self::ONE;
        while e > 0 {
            if e & 1 == 1 {
                r = r.mul(a)
            }
            a = a.mul(a);
            e >>= 1;
        }
        r
    }
    fn inv(self) -> Self {
        // Norm x^(1+p+...+p^4) belongs to Fp after irreducibility certification.
        let mut t = self;
        let mut other = Self::ONE;
        for _ in 0..4 {
            t = t.pow(P);
            other = other.mul(t);
        }
        let norm = self.mul(other);
        assert!(norm.0[1..].iter().all(|x| x.0 == 0));
        other.mixed(norm.0[0].inv())
    }
}
fn trim(a: &mut Vec<M31>) {
    while a.last().is_some_and(|x| x.0 == 0) {
        a.pop();
    }
}
fn rem(mut a: Vec<M31>, b: &[M31]) -> Vec<M31> {
    trim(&mut a);
    let inv = b.last().unwrap().inv();
    while a.len() >= b.len() {
        let k = a.len() - b.len();
        let c = a.last().unwrap().mul(inv);
        for j in 0..b.len() {
            a[j + k] = a[j + k].sub(c.mul(b[j]));
        }
        trim(&mut a);
    }
    a
}
fn qpow(mut a: QM31, mut e: u128) -> QM31 {
    let mut r = QM31::ONE;
    while e > 0 {
        if e & 1 == 1 {
            r = r.mul(a)
        }
        a = a.square();
        e >>= 1;
    }
    r
}
fn u() -> QM31 {
    QM31 {
        c0: CM31::ZERO,
        c1: CM31::ONE,
    }
}
fn times_u(a: QM31) -> QM31 {
    QM31 {
        c0: a.c1.mul(CM31::new(M31(2), M31(1))),
        c1: a.c0,
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Q8(QM31, QM31);
impl Q8 {
    fn mul(self, b: Self) -> Self {
        let a = self.0.mul(b.0);
        let c = self.1.mul(b.1);
        Self(
            a.add(times_u(c)),
            self.0.add(self.1).mul(b.0.add(b.1)).sub(a).sub(c),
        )
    }
    fn square(self) -> Self {
        Self(
            self.0.square().add(times_u(self.1.square())),
            self.0.mul(self.1).add(self.0.mul(self.1)),
        )
    }
    fn mixed(self, b: QM31) -> Self {
        Self(self.0.mul(b), self.1.mul(b))
    }
    fn inv(self) -> Self {
        let n = self.0.square().sub(times_u(self.1.square())).inv();
        Self(self.0.mul(n), self.1.neg().mul(n))
    }
}
fn parse<const N: usize>(bytes: &[u8]) -> Option<[M31; N]> {
    if bytes.len() != N * 4 {
        return None;
    }
    let mut a = [M31(0); N];
    for i in 0..N {
        let v = u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap());
        if v >= P {
            return None;
        }
        a[i] = M31(v);
    }
    Some(a)
}
fn sample<const N: usize>(state: &mut u64) -> [M31; N] {
    // Only sampling/decoding overhead: deterministic synthetic words, NOT a RO/RNG benchmark.
    std::array::from_fn(|_| loop {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        let v = (*state as u32) & P;
        if v < P {
            break M31(v);
        }
    })
}
fn bench<T>(name: &str, n: usize, mut f: impl FnMut() -> T) {
    let mut ns = Vec::new();
    for _ in 0..21 {
        let t = Instant::now();
        for _ in 0..n {
            black_box(f());
        }
        ns.push(t.elapsed().as_nanos() as f64 / n as f64);
    }
    ns.sort_by(f64::total_cmp);
    println!(
        "{name},mean_ns={:.3},p50_batch_ns={:.3},p95_batch_ns={:.3},batches=21,n={n}",
        ns.iter().sum::<f64>() / 21.,
        ns[10],
        ns[19]
    );
}
fn main() {
    // Rabin criterion for prime degree 5: x^(p^5)=x, gcd(x^p-x,f)=1.
    let xp = Q5::X.pow(P);
    let mut a = vec![M31(P - 6), M31(P - 1), M31(0), M31(0), M31(0), M31(1)];
    let mut b = xp.0.to_vec();
    b[1] = b[1].sub(M31(1));
    trim(&mut b);
    while !b.is_empty() {
        let r = rem(a, &b);
        a = b;
        b = r;
    }
    assert_eq!(a.len(), 1);
    let mut x = Q5::X;
    for _ in 0..5 {
        x = x.pow(P)
    }
    assert_eq!(x, Q5::X);
    // Existing tower is i²=-1, u²=2+i. v²=u is irreducible iff u is nonsquare.
    assert_eq!(u().mul(u()), QM31::from_cm31(CM31::new(M31(2), M31(1))));
    assert_eq!(qpow(u(), ((P as u128).pow(4) - 1) / 2), QM31::ONE.neg());
    let mut seed = 123456789u64;
    for _ in 0..1000 {
        let a = Q5(sample(&mut seed));
        let b = Q5(sample(&mut seed));
        let c = Q5(sample(&mut seed));
        assert_eq!(a.mul(b), b.mul(a));
        assert_eq!(a.mul(b).mul(c), a.mul(b.mul(c)));
        assert_eq!(a.mul(a.inv()), Q5::ONE);
        let q = |s: &mut u64| {
            let a = sample::<4>(s);
            QM31 {
                c0: CM31::new(a[0], a[1]),
                c1: CM31::new(a[2], a[3]),
            }
        };
        let a = Q8(q(&mut seed), q(&mut seed));
        let b = Q8(q(&mut seed), q(&mut seed));
        let c = Q8(q(&mut seed), q(&mut seed));
        assert_eq!(a.mul(b), b.mul(a));
        assert_eq!(a.mul(b).mul(c), a.mul(b.mul(c)));
        assert_eq!(a.square(), a.mul(a));
        assert_eq!(a.mul(a.inv()), Q8(QM31::ONE, QM31::ZERO));
        assert_eq!(a.mixed(b.0), a.mul(Q8(b.0, QM31::ZERO)));
    }
    for n in [16, 20, 32] {
        let mut bytes = vec![0; n];
        bytes[..4].copy_from_slice(&P.to_le_bytes());
        match n {
            16 => assert!(parse::<4>(&bytes).is_none()),
            20 => assert!(parse::<5>(&bytes).is_none()),
            _ => assert!(parse::<8>(&bytes).is_none()),
        }
    }
    println!("certification=Rabin-quintic-and-Euler-octic-passed; random_arithmetic_cases=1000; canonical_rejection=passed");
    let a = QM31 {
        c0: CM31::new(M31(11), M31(17)),
        c1: CM31::new(M31(23), M31(29)),
    };
    let b = a.square();
    let x = Q5([M31(2), M31(3), M31(5), M31(7), M31(11)]);
    let y = x.mul(x);
    let z = Q8(a, b);
    // A checked inverse is unique, including on adversarial inputs. Zero fails.
    let hint = a.inv();
    assert_eq!(a.mul(hint), QM31::ONE);
    assert_ne!(a.mul(hint.add(QM31::ONE)), QM31::ONE);
    assert_ne!(QM31::ZERO.mul(hint), QM31::ONE);
    bench("checked_qm31_inverse_hint", 10000, || {
        black_box(a).mul(black_box(hint)) == QM31::ONE
    });
    // Falsification: a K-mask cannot hide the v-coordinate of v*w+r in K(v).
    let narrow_mask = b;
    let public = Q8(narrow_mask, a);
    assert_eq!(public.1, a);
    // An E-mask has an independently variable second coordinate; uniformity
    // and adaptive full-view simulation still require a protocol proof.
    println!(
        "inverse_hint_zero_and_corruption_rejected; narrow_mask_wide_view_counterexample_passed"
    );
    bench("qm31_mul", 10000, || black_box(a).mul(black_box(b)));
    bench("qm31_square", 10000, || black_box(a).square());
    bench("qm31_inv", 1000, || black_box(a).inv());
    bench("qm31_m31", 10000, || {
        black_box(a).mul_m31(black_box(M31(137)))
    });
    bench("q5_mul_reference", 10000, || black_box(x).mul(black_box(y)));
    bench("q5_square_generic", 10000, || {
        black_box(x).mul(black_box(x))
    });
    bench("q5_inv_reference", 100, || black_box(x).inv());
    bench("q5_m31", 10000, || black_box(x).mixed(black_box(M31(137))));
    bench("q8_mul", 10000, || black_box(z).mul(black_box(Q8(b, a))));
    bench("q8_square", 10000, || black_box(z).square());
    bench("q8_inv", 1000, || black_box(z).inv());
    bench("q8_qm31", 10000, || black_box(z).mixed(black_box(b)));
    bench("parse4", 10000, || parse::<4>(black_box(&[3u8; 16])));
    bench("parse5", 10000, || parse::<5>(black_box(&[3u8; 20])));
    bench("parse8", 10000, || parse::<8>(black_box(&[3u8; 32])));
    bench("synthetic_sample4", 10000, || sample::<4>(&mut seed));
    bench("synthetic_sample5", 10000, || sample::<5>(&mut seed));
    bench("synthetic_sample8", 10000, || sample::<8>(&mut seed));
}
