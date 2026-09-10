//! Exact small obstruction to automatic two-regular-branch coprimality.
//! Not a literal selected-parent, support or verifier counterexample.
const P: u64 = 65537;
const N: usize = 17;
type Poly = Vec<u64>;
fn add(a: u64, b: u64) -> u64 { (a + b) % P }
fn sub(a: u64, b: u64) -> u64 { (a + P - b) % P }
fn mul(a: u64, b: u64) -> u64 { a * b % P }
fn pow(mut a: u64, mut n: u64) -> u64 {
    let mut r = 1;
    while n > 0 {
        if n & 1 != 0 { r = mul(r, a); }
        a = mul(a, a); n >>= 1;
    }
    r
}
fn trim(mut a: Poly) -> Poly {
    while a.len() > 1 && a.last() == Some(&0) { a.pop(); }
    a
}
fn plus(a: &[u64], b: &[u64]) -> Poly {
    let mut r = vec![0; a.len().max(b.len())];
    for (i, &x) in a.iter().enumerate() { r[i] = add(r[i], x); }
    for (i, &x) in b.iter().enumerate() { r[i] = add(r[i], x); }
    trim(r)
}
fn scale(a: &[u64], c: u64) -> Poly { trim(a.iter().map(|&x| mul(x, c)).collect()) }
fn times(a: &[u64], b: &[u64]) -> Poly {
    let mut r = vec![0; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() { r[i+j] = add(r[i+j], mul(x, y)); }
    }
    trim(r)
}
fn eval(a: &[u64], x: u64) -> u64 {
    a.iter().rev().fold(0, |r, &c| add(mul(r, x), c))
}
fn compose(a: &[u64], b: &[u64]) -> Poly {
    a.iter().rev().fold(vec![0], |r, &c| plus(&times(&r, b), &[c]))
}
fn cube_coefficient(a: &[Poly], n: usize) -> Poly {
    let mut r = vec![0];
    for i in 1..n {
        for j in 1..n-i {
            let k = n-i-j;
            r = plus(&r, &times(&times(&a[i], &a[j]), &a[k]));
        }
    }
    r
}
// Y^3-Y-T*(X^2-X)=0 at X=0, and X=1+u gives u^2+u.
// All coefficients are exact polynomials in the formal parameter T.
fn branch(at_one: bool) -> Vec<Poly> {
    let mut a = vec![vec![0]; N];
    for n in 1..N {
        let cubic = cube_coefficient(&a, n);
        let forcing = match n {
            1 => vec![0, if at_one { P-1 } else { 1 }],
            2 => vec![0, P-1],
            _ => vec![0],
        };
        a[n] = plus(&cubic, &forcing);
    }
    // Verify every coefficient of the defining equation modulo u^N.
    for n in 0..N {
        let mut coefficient = plus(&cube_coefficient(&a, n), &scale(&a[n], P-1));
        if n == 1 { coefficient = plus(&coefficient, &[0, if at_one { P-1 } else { 1 }]); }
        if n == 2 { coefficient = plus(&coefficient, &[0, P-1]); }
        assert_eq!(coefficient, vec![0]);
    }
    a
}
fn main() {
    let a0 = branch(false); let a1 = branch(true);
    for n in 0..N {
        assert_eq!(a1[n], scale(&a0[n], if n % 2 == 0 { 1 } else { P-1 }));
    }
    let half = pow(2, P-2);
    let at = |a: &[Poly], x: u64| (0..N).fold(vec![0], |r, n|
        plus(&r, &scale(&a[n], pow(x, n as u64))));
    let e0 = at(&a0, half); let e1 = at(&a1, sub(half, 1));
    assert_eq!(e0, e1);
    assert_eq!(e0[0], 0); assert_eq!(e0[1], pow(4, P-2));
    let exponent = 2*(N-1)-1;
    let d0 = scale(&e0, pow(P-1, exponent as u64));
    let d1 = scale(&e1, pow(P-1, exponent as u64));
    assert_eq!(d0, d1); assert_ne!(d0, vec![0]);
    let mut b = vec![1];
    for g in 1..=37 { b = times(&b, &[sub(0, g), 1]); }
    let composed = compose(&d0, &b);
    assert_ne!(composed, vec![0]);
    // T divides D(T), so b(Z) divides D(b(Z)); check that quotient exactly.
    let quotient = compose(&d0[1..], &b);
    assert_eq!(composed, times(&b, &quotient));
    for g in 1..=37 {
        assert_eq!(eval(&b, g), 0);
        assert_eq!(eval(&composed, g), 0);
        // The global specialization admits U(X)=0; both point derivatives -1.
        let bg = eval(&b, g);
        assert_eq!(vec![0, bg, sub(0, bg)], vec![0; 3]);
        for x in [0, 1] {
            assert_eq!(sub(0, mul(bg, mul(x, sub(x, 1)))), 0);
            assert_eq!(sub(mul(3, mul(0, 0)), 1), P-1);
        }
    }
    println!("PASS field={} truncation_length={} hensel_exponent={} both_regular_derivatives=-1", P, N, exponent);
    println!("PASS exact_formal_parameter_series=true reflected_coefficients={} center_discrepancies_identical=true", N);
    println!("PASS parameter_discrepancy_degree={} b_degree={} composed_discrepancy_degree={} exact_b_divisor=true common_roots=37", d0.len()-1, b.len()-1, composed.len()-1);
    println!("SCOPE algebraic retained cubic and finite Hensel discrepancies; irreducibility proof in report; NOT literal canonical parent, selected encoder, middle support, earlyC1-none, semantic acceptance, or probability");
}
