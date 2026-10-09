// Source-only focused control, NOT Y>=3 acceptance or payment soundness.
// Reuses literal V7 circle slot order, normalized nested butterfly,
// natural8/final2 coefficient order, image weights, dual fold and six-field
// compact Horner. Compile only with rustc -O -C overflow-checks=yes, in a
// separately capped scope after a compiler grant. No package build needed.
// Exhaustive scope: F31 alphas/kappas/taus, all 210 ordered distinct q3
// schedules on seven nondegenerate circle fibres. No search over strategies.

const P: usize = 31;
const T: usize = 7;
const FULL: usize = 6;
type Point = (usize, usize);

fn add(a: usize, b: usize) -> usize { (a + b) % P }
fn sub(a: usize, b: usize) -> usize { (a + P - b) % P }
fn mul(a: usize, b: usize) -> usize { a * b % P }
fn pow(mut a: usize, mut n: usize) -> usize {
    let mut r = 1;
    while n != 0 {
        if n & 1 != 0 { r = mul(r, a); }
        a = mul(a, a); n >>= 1;
    }
    r
}
fn inv(a: usize) -> usize { assert_ne!(a, 0); pow(a, P - 2) }
fn slots((x, y): Point) -> [Point; 4] {
    [(x, y), (x, sub(0, y)), (sub(0, x), sub(0, y)), (sub(0, x), y)]
}
fn fibres() -> [Point; T] {
    let mut seen = [[false; P]; P];
    let mut out = Vec::new();
    for x in 1..P { for y in 1..P {
        if add(mul(x, x), mul(y, y)) == 1 && !seen[x][y] {
            out.push((x, y));
            for (a, b) in slots((x, y)) { seen[a][b] = true; }
        }
    }}
    out.try_into().unwrap()
}
fn radix4((x, y): Point, c: [usize; 4]) -> [usize; 4] {
    slots((x, y)).map(|(a, b)|
        add(add(c[0], mul(b, c[1])), add(mul(a, c[2]), mul(mul(a, b), c[3]))))
}
fn pair_fold(alpha: usize, inverse: usize, left: usize, right: usize) -> usize {
    add(mul(add(left, right), inv(2)), mul(alpha, mul(sub(left, right), inverse)))
}
fn circle_fold((x, y): Point, values: [usize; 4], alpha: usize) -> usize {
    let left = pair_fold(alpha, inv(mul(2, y)), values[0], values[1]);
    let right = pair_fold(alpha, sub(0, inv(mul(2, y))), values[2], values[3]);
    pair_fold(pow(alpha, 2), inv(mul(2, x)), left, right)
}
fn basis((x, y): Point) -> [usize; 8] {
    let t = sub(mul(2, mul(x, x)), 1);
    [1, y, x, mul(x, y), t, mul(y, t), mul(x, t), mul(mul(x, y), t)]
}
fn rank(mut matrix: Vec<[usize; 8]>) -> usize {
    let mut row = 0;
    for col in 0..8 {
        let Some(pivot) = (row..matrix.len()).find(|&r| matrix[r][col] != 0) else { continue; };
        matrix.swap(row, pivot);
        let scale = inv(matrix[row][col]);
        for j in col..8 { matrix[row][j] = mul(matrix[row][j], scale); }
        for r in 0..matrix.len() {
            if r == row { continue; }
            let scale = matrix[r][col];
            for j in col..8 { matrix[r][j] = sub(matrix[r][j], mul(scale, matrix[row][j])); }
        }
        row += 1;
    }
    row
}
fn image_weights(kappa: usize, tau: usize) -> [usize; 8] {
    // Fixed arbitrary original rows; they are NOT the selected ten-bit MLE rows.
    let mut w = std::array::from_fn(|i| {
        let rows = [i % P, (i + 1) % P, (2 * i + 3) % P, (3 * i + 5) % P];
        (0..4).fold(0, |s, j| add(s, mul(pow(kappa, j), rows[j])))
    });
    w[7] = add(w[7], tau);
    w[6] = add(w[6], mul(pow(tau, 2), 2));
    w[5] = sub(w[5], mul(pow(tau, 2), 3));
    w
}
fn dual_fold(alpha: usize, w: [usize; 4]) -> usize {
    mul(add(add(w[0], mul(pow(alpha, 3), w[1])),
        add(mul(pow(alpha, 2), w[2]), mul(alpha, w[3]))), inv(4))
}
fn compact_horner(claim: usize, sent: [usize; 6], alpha: usize) -> usize {
    // Six source fields c0,c1,c2,c3,c5,c6; c4 is never supplied.
    let coefficients = [sent[0], sent[1], sent[2], sent[3],
        sub(mul(claim, inv(4)), sent[0]), sent[4], sent[5]];
    coefficients.into_iter().rev().fold(0, |r, c| add(c, mul(alpha, r)))
}
fn falling(n: usize) -> u64 { (n * (n - 1) * (n - 2)) as u64 }

fn main() {
    let points = fibres();
    assert_eq!(rank(points[..2].iter().flat_map(|&p| slots(p)).map(basis).collect()), 8);
    // These two zero full fibres force the natural8 candidate to be zero.
    // The seventh received fibre is nonzero, hence this word is not itself
    // a natural8 codeword. The small strong-support threshold is all7 fibres.
    let received: [[usize; 4]; T] = std::array::from_fn(|i| {
        if i < FULL { [0; 4] } else { radix4(points[i], [0, P - 1, 0, 1]) }
    });
    assert!(received[FULL].iter().any(|&v| v != 0));
    // Actual first response is committed before alpha; no alpha-dependent
    // repair or replacement is made. The actual final is also zero.
    let sent_before_alpha = [0; 6];
    let final_after_alpha = [0; 2];
    let mut prior_checks = 0;
    for kappa in 0..P { for tau in 0..P {
        let w = image_weights(kappa, tau);
        for alpha in 0..P {
            let carried = compact_horner(0, sent_before_alpha, alpha);
            let dot = (0..2).fold(0, |s, j| add(s, mul(final_after_alpha[j],
                dual_fold(alpha, w[4*j..4*j+4].try_into().unwrap()))));
            assert_eq!(sub(carried, dot), 0);
            prior_checks += 1;
        }
    }}
    let mut hits = 0_u64;
    let mut checked_schedules = 0_u64;
    let mut three_roots = 0;
    for alpha in 0..P {
        let expected_bad = sub(pow(alpha, 3), alpha);
        let matches: [bool; T] = std::array::from_fn(|i| {
            let folded = circle_fold(points[i], received[i], alpha);
            assert_eq!(folded, if i < FULL { 0 } else { expected_bad });
            folded == 0
        });
        if expected_bad == 0 { three_roots += 1; }
        for i in 0..T { for j in 0..T { for k in 0..T {
            if i == j || i == k || j == k { continue; }
            checked_schedules += 1;
            hits += u64::from(matches[i] && matches[j] && matches[k]);
        }}}
    }
    assert_eq!(three_roots, 3);
    assert_eq!(checked_schedules, P as u64 * falling(T));
    let exact_numerator = 3 * falling(T) + (P as u64 - 3) * falling(FULL);
    assert_eq!(hits, exact_numerator);
    assert_eq!((hits, checked_schedules, prior_checks), (3990, 6510, 29791));
    println!("PASS actual_radix4_fold alpha_roots={three_roots} causal_prior_checks={prior_checks} ordered_schedule_checks={checked_schedules}");
    println!("EXACT compatible_moment={hits}/{checked_schedules}=19/31 beta=4/7 upper=beta+(1-beta)*3/31 SATURATED");
    println!("SCOPE one fixed reduced F31 strategy; source-order fold and compact-response control, not selected higher-factor/kernel/authentication/payment acceptance; no gamma or FS probability claim");
}
