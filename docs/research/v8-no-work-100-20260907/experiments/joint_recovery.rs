//! Full-fibre boundary falsifier. Not a payment forgery or an adaptive ZK proof.
#![allow(dead_code)]
extern crate alloc;
#[path = "../../../../crates/aspis-core/src/field.rs"] mod field;
#[path = "../../../../crates/aspis-core/src/params.rs"] mod params;
#[path = "../../../../crates/aspis-core/src/circle.rs"] mod circle;
use field::{M31, CM31, QM31 as K};
const T: usize = 1 << 18;
const J: usize = 9557;
fn embed(x: M31) -> K { K::from_cm31(CM31::new(x, M31::ZERO)) }
fn parameter(n: u32) -> K {
    K { c0: CM31::new(M31(n), M31(3)), c1: CM31::new(M31(5), M31(7)) }
}
fn polynomial(index: usize) -> [M31; 29] {
    let mut p = [M31::ZERO; 29]; p[0] = M31::ONE;
    for j in 0..28 {
        let root = M31((28 * index + j + 1) as u32);
        let mut next = [M31::ZERO; 29];
        for k in 0..=j {
            next[k] = next[k].sub(root.mul(p[k]));
            next[k+1] = next[k+1].add(p[k]);
        }
        p = next;
    }
    p
}
fn mixed_dot(p: &[M31; 29], gamma: K) -> K {
    let mut power = K::ONE; let mut sum = K::ZERO;
    for (j, v) in p.iter().enumerate() {
        sum = sum.add(if j < 26 { power.mul_m31(*v) } else { power.mul(embed(*v)) });
        power = power.mul(gamma);
    }
    sum
}
// Literal selected nested circle fold. Does not import the parser or transcript.
fn fold(v: [K; 4], x: M31, y: M31, alpha: K) -> K {
    let ix = x.double().inv(); let iy = y.double().inv();
    let positive = v[0].add(v[1]).half().add(alpha.mul(v[0].sub(v[1]).mul_m31(iy)));
    let negative = v[2].add(v[3]).half().add(alpha.mul(v[2].sub(v[3]).mul_m31(iy.neg())));
    positive.add(negative).half().add(alpha.square().mul(positive.sub(negative).mul_m31(ix)))
}
fn main() {
    assert_eq!(28 * (T-J), 7_072_436);
    assert!(28 * (T-J) < field::P as usize);
    assert!(4*J > 1024 && 4*(J+1) > 38229 && J+1 > 9557);
    let p0 = circle::secure_ood_circle_point_from_parameter(parameter(11)).unwrap();
    let p1 = circle::secure_ood_circle_point_from_parameter(parameter(29)).unwrap();
    let a = p0.x.mul(p1.y).sub(p0.y.mul(p1.x));
    let b = p0.y.sub(p1.y); let c = p1.x.sub(p0.x);
    let alphas = [K::ZERO, K::ONE, K::ONE.neg(), parameter(31), parameter(71)];
    let mut dots = 0; let mut folds = 0;
    for sample in 0..66 {
        let s = sample * (T-J-1) / 65;
        let p = polynomial(s);
        assert_eq!(p[28], M31::ONE);
        // Source circle_domain_point_for_log(20, 4*fibre): reverse20(4*fibre).
        let fibre = J+s;
        let natural = (4*fibre).reverse_bits() >> (usize::BITS-20);
        let point = params::CIRCLE_GEN.pow((1u64 << 10) + (1u64 << 12)*natural as u64);
        assert_ne!(point.a, M31::ZERO); assert_ne!(point.b, M31::ZERO);
        let coords = [(point.a, point.b), (point.a, point.b.neg()),
            (point.a.neg(), point.b.neg()), (point.a.neg(), point.b)];
        for j in 1..=28 {
            let gamma = embed(M31((28*s+j) as u32));
            let value = mixed_dot(&p, gamma); dots += 1;
            assert_eq!(value, K::ZERO);
            let q = coords.map(|(x,y)| {
                let l = a.add(b.mul_m31(x)).add(c.mul_m31(y));
                assert_ne!(l, K::ZERO);
                value.mul(l.try_inv().unwrap())
            });
            for alpha in alphas {
                assert_eq!(fold(q, point.a, point.b, alpha), K::ZERO); folds += 1;
            }
        }
        // An adjacent interval does not accidentally vanish here.
        let other = if s == 0 { 28*(T-J) } else { 28*s };
        assert_ne!(mixed_dot(&p, embed(M31(other as u32))), K::ZERO); dots += 1;
    }
    println!("PASS {dots} production mixed-width dots; {folds} chord/fold checks; 66 boundary intervals");
    println!("Symbolic disjoint-interval count = 7072436; common fibres = 9557; matched fibres = 9558; matched symbols = 38232");
    println!("All-alpha zero folding holds by linearity; all intervals by the product formula, not sampling.");
    println!("REFUTED: <=2800 bad gammas for unconditional same-support recovery even after both agreement gates.");
    println!("NOT a full accepted proof; no authentication, semantic, FS or hiding result.");
}
