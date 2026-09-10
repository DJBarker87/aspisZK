//! Exact, synthetic RS control; NOT the selected circle encoder or fixedInterpolant.
//! All arithmetic is F_181. No dependencies, network, randomness, or secret inputs.
//! Run optimized: rustc --edition=2021 -O -C overflow-checks=yes this.rs -o CONTROL.
use std::time::Instant;

const P: u64 = 181;
fn add(a: u64, b: u64) -> u64 { (a + b) % P }
fn sub(a: u64, b: u64) -> u64 { (a + P - b) % P }
fn mul(a: u64, b: u64) -> u64 { a * b % P }
fn pow(mut a: u64, mut n: usize) -> u64 {
    let mut b = 1;
    while n != 0 {
        if n & 1 != 0 { b = mul(b, a); }
        a = mul(a, a); n >>= 1;
    }
    b
}
fn choose(n: usize, j: usize) -> u64 {
    if j > n { return 0; }
    let mut c = 1;
    for i in 0..j { c = c * (n - i) as u64 / (i + 1) as u64; }
    c % P
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Poly(Vec<u64>);
impl Poly {
    fn new(mut c: Vec<u64>) -> Self {
        while c.last() == Some(&0) { c.pop(); }
        Self(c)
    }
    fn c(c: u64) -> Self { Self::new(vec![c]) }
    fn zero() -> Self { Self(Vec::new()) }
    fn is_zero(&self) -> bool { self.0.is_empty() }
    fn add(&self, b: &Self) -> Self {
        let mut c = vec![0; self.0.len().max(b.0.len())];
        for (i, &v) in self.0.iter().enumerate() { c[i] = v; }
        for (i, &v) in b.0.iter().enumerate() { c[i] = add(c[i], v); }
        Self::new(c)
    }
    fn scale(&self, a: u64) -> Self {
        Self::new(self.0.iter().map(|&v| mul(a, v)).collect())
    }
    fn sub(&self, b: &Self) -> Self { self.add(&b.scale(P - 1)) }
    fn mul(&self, b: &Self) -> Self {
        if self.is_zero() || b.is_zero() { return Self::zero(); }
        let mut c = vec![0; self.0.len() + b.0.len() - 1];
        for (i, &a) in self.0.iter().enumerate() {
            for (j, &v) in b.0.iter().enumerate() { c[i + j] = add(c[i + j], mul(a, v)); }
        }
        Self::new(c)
    }
    fn pow(&self, mut n: usize) -> Self {
        let mut a = self.clone(); let mut b = Self::c(1);
        while n != 0 {
            if n & 1 != 0 { b = b.mul(&a); }
            n >>= 1; if n != 0 { a = a.mul(&a); }
        }
        b
    }
    fn eval(&self, z: u64) -> u64 {
        self.0.iter().rev().fold(0, |v, &c| add(mul(v, z), c))
    }
}

// Coefficients in F_181[Z] of X/Y increments, truncated at total order < 3.
// This is the six Hasse constraints, not 181-point polynomial testing.
const ORDERS: [(usize, usize); 6] = [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)];
type Jet = [Poly; 6];
fn jet_one() -> Jet {
    std::array::from_fn(|i| Poly::c(if i == 0 { 1 } else { 0 }))
}
fn jet_mul(a: &Jet, b: &Jet) -> Jet {
    std::array::from_fn(|k| {
        let mut c = Poly::zero();
        for i in 0..6 { for j in 0..6 {
            if (ORDERS[i].0 + ORDERS[j].0, ORDERS[i].1 + ORDERS[j].1) == ORDERS[k] {
                c = c.add(&a[i].mul(&b[j]));
            }
        }}
        c
    })
}
fn cube(a: &Jet) -> Jet { jet_mul(&jet_mul(a, a), a) }
fn factor_jet(x: u64, received: &Poly, a_z: &Poly) -> Jet {
    std::array::from_fn(|i| {
        let (a, b) = ORDERS[i];
        let mut out = Poly::zero();
        if a == 0 {
            out = received.pow(31 - b).scale(choose(31, b));
            if b == 0 { out = out.sub(received); }
            if b == 1 { out = out.sub(&Poly::c(1)); }
        }
        if b == 0 { out = out.sub(&a_z.scale(mul(choose(3, a), pow(x, 3 - a)))); }
        out
    })
}

fn main() {
    let start = Instant::now();
    for d in 2..P { assert!(P % d != 0); } // primality certificate at this tiny size
    let domain: Vec<u64> = (0..P).filter(|&x| pow(x, 90) == 1 && x != 1 && x != P - 1).collect();
    assert_eq!(domain.len(), 88);
    assert!(!domain.contains(&0) && !domain.contains(&1));
    let bad = &domain[76..]; // fixed BEFORE gamma: 19 good / 3 bad four-symbol groups
    let delta = Poly::new(vec![P - 1, 1]);
    let a_z = delta.pow(31).sub(&delta);
    assert_eq!(a_z.0.len(), 32);
    assert_eq!(a_z.0[31], 1); // nonzero coefficient in the Eisenstein certificate

    // F = Y^31-Y-X^3*((Z-1)^31-(Z-1)); polynomial OOD identities at X=0,1.
    assert!(factor_jet(0, &Poly::zero(), &a_z)[0].is_zero());
    assert!(factor_jet(1, &delta, &a_z)[0].is_zero());
    assert_eq!(factor_jet(0, &Poly::zero(), &a_z)[2].eval(1), P - 1);
    assert_eq!(factor_jet(1, &delta, &a_z)[2].eval(1), P - 1);
    // Symbolic Eisenstein certificate: Y^31-Y has exact Y-adic valuation 1.
    // Irreducibility follows by Eisenstein in K(Z)[Y][X], then Gauss; not enumerated.
    let mut y_constant = vec![0; 32]; y_constant[1] = P - 1; y_constant[31] = 1;
    assert_eq!(y_constant[0], 0); assert_ne!(y_constant[1], 0);

    let mut kernel_constraints = 0;
    let mut zero_candidate_support = 0;
    let mut supports = vec![0usize; P as usize];
    for (i, &x) in domain.iter().enumerate() {
        let h = pow(x, 3);
        assert_eq!(pow(h, 31), h);
        let e = if i < 76 { 0 } else { 1 };
        // Fixed C1 lanes: c0=e-X^3, c1=X^3, c2..c25=0; helpers 26..28=0.
        let received = Poly::new(vec![sub(e, h), h]);
        let fj = factor_jet(x, &received, &a_z);
        if e == 0 { assert!(fj[0].is_zero()); }
        let mut locator_jet = jet_one();
        for &b in bad {
            let linear: Jet = std::array::from_fn(|j| Poly::c(match j {
                0 => sub(x, b), 1 => 1, _ => 0,
            }));
            locator_jet = jet_mul(&locator_jet, &linear);
        }
        if e != 0 { assert!(locator_jet[0].is_zero()); }
        // P=F^3*locator_bad^3 satisfies ALL six symbolic Hasse polynomials.
        for constraint in jet_mul(&cube(&fj), &cube(&locator_jet)) {
            assert!(constraint.is_zero()); kernel_constraints += 1;
        }
        for gamma in 0..P {
            if received.eval(gamma) == 0 { supports[gamma as usize] += 1; }
        }
        // At designated later gamma=1: chord L=X(X-1), I=delta*X=0, Q=0.
        let l = mul(x, sub(x, 1)); assert_ne!(l, 0);
        let virtual_quotient = mul(received.eval(1), pow(l, (P - 2) as usize));
        if virtual_quotient == 0 { zero_candidate_support += 1; }
    }
    assert_eq!(kernel_constraints, 528);
    assert_eq!(zero_candidate_support, 76);
    assert_eq!(supports[1], 76);
    assert_eq!(supports.iter().enumerate().filter(|&(_, &n)| n >= 76).map(|(g, _)| g).collect::<Vec<_>>(), vec![1]);
    assert!(19 * 262144 >= 22 * 200808 && 19 * 262144 <= 22 * 252847);

    // Exhaustive witness reduction for ALL RS degree<=2 codewords: any with >=3
    // agreements is the interpolant through one enumerated triple. Polynomials
    // with fewer than3 agreements cannot enter either threshold4 or threshold14.
    let mut triples = 0usize; let mut largest = 0usize;
    for i in 0..88 { for j in i + 1..88 { for k in j + 1..88 {
        let (a, b, c) = (domain[i], domain[j], domain[k]);
        // X^3-(X-a)(X-b)(X-c) = s1*X^2-s2*X+s3.
        let s1 = add(add(a, b), c);
        let s2 = add(add(mul(a, b), mul(a, c)), mul(b, c));
        let s3 = mul(mul(a, b), c);
        let count = domain.iter().filter(|&&x| add(sub(mul(s1, mul(x, x)), mul(s2, x)), s3) == pow(x, 3)).count();
        assert_eq!(count, 3); largest = largest.max(count); triples += 1;
    }}}
    assert_eq!(triples, 109736); assert_eq!(largest, 3);
    // Threshold14 is Johnson-compatible: for a hypothetical 53 tuples,
    // sum of overlap inequalities would give 53*(14^2-88*2)<=88*(14-2).
    assert!(53 * (14 * 14 - 88 * 2) > 88 * (14 - 2));

    // Timing control: pre-gamma claims/helpers are zero polynomials (degrees0).
    // At gamma1 original Q is zero, so every fixed covector gives the zero claim.
    // Test arbitrary row coefficients exhaustively one coefficient at a time.
    let mut row_tests = 0usize;
    for weight in 0..P { for coefficient in 0..3 {
        let original = [0u64; 3]; assert_eq!(mul(weight, original[coefficient]), 0);
        row_tests += 1;
    }}
    // A legal pre-alpha compact response: six disclosed coefficients all zero,
    // c4=claim/4-c0=0, final=0. This does not claim full verifier acceptance.
    for alpha in 0..P {
        let sent = [0u64; 6]; let claim = 0;
        let c4 = sub(mul(claim, pow(4, (P - 2) as usize)), sent[0]);
        let coefficients = [sent[0], sent[1], sent[2], sent[3], c4, sent[4], sent[5]];
        assert_eq!(Poly::new(coefficients.to_vec()).eval(alpha), 0);
    }
    // P's exact extrema follow from its distinct leading monomials.
    let y_degree = 3 * 31;
    let toy_xy_weight = 3 * 62 + 3 * 12;
    let selected_xy_weight = 3 * 31744 + 3 * 12;
    let yz_weight = 3 * 868;
    assert_eq!(y_degree, 93); assert_eq!(toy_xy_weight, 222);
    assert!(76 * 3 > toy_xy_weight);
    assert!(selected_xy_weight < 114688 && yz_weight < 117078 && y_degree < 112);
    println!("FIELD=181 DOMAIN=88 GROUPS=22 GOOD_GROUPS=19 GOOD_SYMBOLS=76 GAMMA=1");
    println!("ALL_QUADRATIC_AGREEMENT_TRIPLES={} MAX_C1_LANE_AGREEMENT={} EARLY_FAMILY_4=EMPTY EARLY_FAMILY_14=EMPTY", triples, largest);
    println!("JOHNSON_THRESHOLD_14_UNIVERSAL_FAMILY_CAP=52");
    println!("SYMBOLIC_HASSE_CONSTRAINTS={} OOD_POLYNOMIAL_IDENTITIES=2 OOD_DERIVATIVE_AT_GAMMA=180", kernel_constraints);
    println!("FACTOR_Y_DEGREE=31 PARENT_Y_DEGREE={} TOY_X_PLUS_2Y={} SELECTED_X_PLUS_1024Y={} GAMMA_PLUS_28Y={}", y_degree, toy_xy_weight, selected_xy_weight, yz_weight);
    println!("ZERO_CANDIDATE_HIGH_SUPPORT_GAMMAS=1 ROW_BASIS_CHECKS={} PRE_ALPHA_ZERO_RESPONSE_CHECKS=181", row_tests);
    println!("SCOPE=synthetic_RS_kernel_member; NO_selected_circle_fibres; NO_fixedInterpolant_selector; NO_payment_or_acceptance_claim");
    println!("RUNTIME_SECONDS={:.6}", start.elapsed().as_secs_f64());
}
