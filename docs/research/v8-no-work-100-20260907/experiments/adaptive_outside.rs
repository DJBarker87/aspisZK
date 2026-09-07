//! Pre-OOD committed T_512 obstruction to query-only adaptive outside tails.
//! New hypothesis vs chord.rs: f is fixed before BOTH OOD points, not Q afterward.
//! No full verifier acceptance, payment forgery, CU or privacy claim.
#![allow(dead_code)]
extern crate alloc;
#[path = "../../../../crates/aspis-core/src/circle.rs"]
mod circle;
#[path = "../../../../crates/aspis-core/src/field.rs"]
mod field;
use circle::{secure_ood_circle_point_from_parameter as ood, SecureCirclePoint as Point};
use field::{CM31, M31, QM31 as K};
#[path = "../../../../crates/aspis-core/src/params.rs"] mod params;
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
fn check_fold(q: &[K], i: K, alpha: K) {
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
    let alpha2 = alpha.square();
    let folded: Vec<K> = (0..N / 2)
        .map(|j| {
            a[2 * j]
                .add(alpha.mul(b[2 * j]))
                .add(alpha2.mul(a[2 * j + 1].add(alpha.mul(b[2 * j + 1]))))
        })
        .collect();
    for fibre in [0usize, 1, 2, 15, 255, 256, 4095, 16383, 131072, 262143] {
        let natural = (4*fibre).reverse_bits() >> (usize::BITS-20);
        let base = params::CIRCLE_GEN.pow((1u64<<10) + (1u64<<12)*natural as u64);
        let p = Point { x: scalar(base.a.0), y: scalar(base.b.0) };
        assert_ne!(p.x, K::ZERO); assert_ne!(p.y, K::ZERO);
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
fn t512(mut x: K) -> K {
    for _ in 0..9 { let s=x.square(); x=s.add(s).sub(K::ONE); }
    x
}
fn main() {
    let i=K::from_cm31(CM31::new(M31::ZERO,M31::ONE));
    assert_eq!(i.square(), K::ONE.neg());
    let half=scalar(2).try_inv().unwrap();
    let inv2i=i.neg().mul(half);
    let s=ood(parameter(11)).unwrap();
    let t=ood(parameter(29)).unwrap();
    let pairs=[
        [s,t], [t,s],
        [s,Point{x:s.x,y:s.y.neg()}],
        [ood(parameter(43)).unwrap(),ood(parameter(79)).unwrap()],
    ];
    let gammas=[K::ONE, scalar(7), parameter(31), parameter(71)];
    let alphas=[K::ZERO,K::ONE,K::ONE.neg(),parameter(37)];
    let mut fold_checks=0;
    for [s,t] in pairs {
        let a=s.x.mul(t.y).sub(s.y.mul(t.x));
        let b=s.y.sub(t.y); let c=t.x.sub(s.x);
        let lo=b.mul(half).sub(c.mul(inv2i));
        let hi=b.mul(half).add(c.mul(inv2i));
        assert_ne!(lo,K::ZERO); assert_ne!(hi,K::ZERO);
        let z0=s.x.add(i.mul(s.y)); let z1=t.x.add(i.mul(t.y));
        assert_eq!(eval(&[lo,a,hi],z0),K::ZERO);
        assert_eq!(eval(&[lo,a,hi],z1),K::ZERO);
        // A C1 lane is fixed to f=T_512(x), all other lanes zero.
        // Test both semantic lane 0 and mask-only lane 25 below.
        // Its OOD answers depend on the point just received, not on future points.
        let v0=t512(s.x); let v1=t512(t.x);
        assert_eq!(v0,pow(z0,N).add(pow(z0,N).try_inv().unwrap()).mul(half));
        assert_eq!(v1,pow(z1,N).add(pow(z1,N).try_inv().unwrap()).mul(half));
        let use_x=s.x!=t.x;
        let h0=if use_x{s.x}else{s.y}; let h1=if use_x{t.x}else{t.y};
        let slope=v0.sub(v1).mul(h0.sub(h1).try_inv().unwrap());
        let intercept=v0.sub(slope.mul(h0));
        let (il,ih)=if use_x{(slope.mul(half),slope.mul(half))}
            else{(slope.mul(inv2i).neg(),slope.mul(inv2i))};
        // z^512 * (f-I): f=(z^512+z^-512)/2, independent of the OOD pair.
        let mut rem=vec![K::ZERO;2*N+1];
        rem[0]=half; rem[2*N]=half;
        rem[N]=intercept.neg(); rem[N-1]=il.neg(); rem[N+1]=ih.neg();
        let numerator=rem.clone();
        let mut q=vec![K::ZERO;2*N-1];
        let invhi=hi.try_inv().unwrap();
        for j in (2..rem.len()).rev() {
            let v=rem[j].mul(invhi); q[j-2]=v; rem[j]=K::ZERO;
            rem[j-1]=rem[j-1].sub(v.mul(a)); rem[j-2]=rem[j-2].sub(v.mul(lo));
        }
        assert!(rem.iter().all(|v|*v==K::ZERO));
        let mut rebuilt=vec![K::ZERO;2*N+1];
        for (j,v) in q.iter().enumerate() {
            for (d,l) in [lo,a,hi].iter().enumerate(){rebuilt[j+d]=rebuilt[j+d].add(v.mul(*l));}
        }
        assert_eq!(rebuilt,numerator);
        // Unlike honest W, this reconstructed f has nonzero extreme SUM.
        assert_eq!(hi.mul(q[2*N-2]).add(lo.mul(q[0])),K::ONE);
        // Membership is not certified by quotient degree alone.
        for lane in [0usize,25] { for gamma in gammas {
            assert_ne!(gamma,K::ZERO);
            let scale=pow(gamma,lane); assert_ne!(scale,K::ZERO);
            let scaled:Vec<K>=q.iter().map(|v|v.mul(scale)).collect();
            assert_eq!(hi.mul(scaled[2*N-2]).add(lo.mul(scaled[0])),scale);
            // New joint-image continuation: top natural-tensor coefficients.
            // Leading Chebyshev/tensor ratio is 256; B's degree is <=510,
            // hence q[1023]=0. This checks the explicit E2=512*gamma^lane,
            // not merely an unspecified Laurent endpoint overflow.
            let top_a=scaled[2*N-2].add(scaled[0]).mul(scalar(256));
            let next_b=i.mul(scaled[2*N-2].sub(scaled[0])).mul(scalar(256));
            assert_eq!(b.mul(top_a).sub(c.mul(next_b)),scalar(512).mul(scale));
            for alpha in alphas {check_fold(&scaled,i,alpha); fold_checks+=10;}
        }}
    }
    // Canonical base-field C1 data fixed independently of OOD challenges.
    for fibre in [0usize,1,255,4095,131072,262143] {
        let natural=(4*fibre).reverse_bits()>>(usize::BITS-20);
        let point=params::CIRCLE_GEN.pow((1u64<<10)+(1u64<<12)*natural as u64);
        let mut base=point.a;
        for _ in 0..9 {base=base.mul(base).double().sub(M31::ONE);}
        assert_eq!(t512(scalar(point.a.0)),scalar(base.0));
    }
    println!("PASS 4 legal OOD pairs, including equal-x and reversed endpoints");
    println!("PASS exact coefficientwise chord division/reconstruction for precommitted T_512");
    println!("PASS {fold_checks} actual-domain nested-fold comparisons against degree<=255 final polynomials");
    println!("PASS all 32 gamma-scaled overflow residuals nonzero; semantic lane 0 and mask-only lane 25; zero alpha included");
    println!("PASS all 32 natural-tensor E2=512*gamma^lane residual identities (new image-gate continuation)");
    println!("UNIVERSAL DERIVATION: Q is in Laurent[-511,511], f is outside W; M=T for every legal OOD pair and nonzero gamma and every alpha");
    println!("This is a query-only obstruction. Required image/relation checks may reject it. NOT full verifier acceptance.");
}
