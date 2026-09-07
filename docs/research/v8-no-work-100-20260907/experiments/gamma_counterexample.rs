//! Exact malicious-oracle construction against an UNCONDITIONAL 28-gamma recovery bound.
//! Not a counterexample to the fixed-tuple theorem or a complete payment forgery.
#![allow(dead_code)]
extern crate alloc;
#[path = "../../../../crates/aspis-core/src/field.rs"]
mod field;
use field::{CM31, M31, QM31 as K};
const FIBRES: usize = 1 << 18;
const GAMMAS: usize = 760;
const ROOTS: usize = 28;
fn eval(p: &[M31; 29], x: M31) -> M31 {
    p.iter().rev().fold(M31::ZERO, |s, c| s.mul(x).add(*c))
}
fn main() {
    let mut patterns = Vec::new();
    for start in 0..GAMMAS {
        let mut p = [M31::ZERO; 29];
        p[0] = M31::ONE;
        for j in 0..ROOTS {
            let root = M31(((start + j) % GAMMAS + 1) as u32);
            let mut next = [M31::ZERO; 29];
            for k in 0..=j {
                next[k] = next[k].sub(root.mul(p[k]));
                next[k + 1] = next[k + 1].add(p[k]);
            }
            p = next;
        }
        assert_eq!(p[28], M31::ONE);
        // Independent evaluation checks both the promised roots and all other selected gammas.
        for g in 0..GAMMAS {
            let expected = (g + GAMMAS - start) % GAMMAS < ROOTS;
            assert_eq!(eval(&p, M31((g + 1) as u32)) == M31::ZERO, expected);
        }
        patterns.push(p);
    }
    let mut supports = [0usize; GAMMAS];
    for fibre in 0..FIBRES {
        for j in 0..ROOTS {
            supports[(fibre + j) % GAMMAS] += 1;
        }
    }
    let lo = *supports.iter().min().unwrap();
    let hi = *supports.iter().max().unwrap();
    assert!(lo > 9557);
    assert!(4 * lo > 38229);
    assert_eq!(supports.iter().sum::<usize>(), ROOTS * FIBRES);
    // Independent production-width gamma dot: columns 0..25 are M31;
    // H/G/D are columns 26/27/28 embedded in K. D is identically one.
    for (start, p) in patterns.iter().enumerate() {
        let g = M31((start + 1) as u32);
        let gamma = K::from_cm31(CM31::new(g, M31::ZERO));
        let mut power = K::ONE;
        let mut sum = K::ZERO;
        for (j, c) in p.iter().enumerate() {
            sum = sum.add(if j < 26 {
                power.mul_m31(*c)
            } else {
                power.mul(K::from_cm31(CM31::new(*c, M31::ZERO)))
            });
            power = power.mul(gamma);
        }
        assert_eq!(sum, K::ZERO);
    }
    println!(
        "PASS {} exact polynomial evaluations; {} production-width gamma dots",
        GAMMAS * GAMMAS,
        GAMMAS
    );
    println!("N_fibres={FIBRES}, gamma_set={GAMMAS}, roots_per_fibre={ROOTS}, min_support={lo}, max_support={hi}, min_initial_symbols={}",4*lo);
    println!("D=1 at every position; claiming D=0 at both OOD points is false for every coherent D extraction");
    println!("Each selected gamma has a zero codeword/zero chord quotient on more than the agreement threshold");
    println!("REFUTED: initial combined agreement plus two claimed OOD vectors alone implies <=28 bad gammas");
    println!("NOT REFUTED: conditional fixed-tuple theorem; NOT a complete verifier forgery or 100-bit attack");
    // Symbol-level variant is specified by disjoint root intervals. Avoid a
    // million redundant expansions: verify endpoints and 64 deterministic cases;
    // the all-pattern guarantee follows from the explicit product formula.
    let outside = (1usize << 20) - 38229;
    let mut examples = vec![0, outside - 1];
    examples.extend((0..64).map(|j| j * (outside - 1) / 63));
    for index in examples {
        let mut p = [M31::ZERO; 29];
        p[0] = M31::ONE;
        for j in 0..28 {
            let root = M31((28 * index + j + 1) as u32);
            let mut next = [M31::ZERO; 29];
            for k in 0..=j {
                next[k] = next[k].sub(root.mul(p[k]));
                next[k + 1] = next[k + 1].add(p[k]);
            }
            p = next;
        }
        assert_eq!(p[28], M31::ONE);
        for j in 0..28 {
            assert_eq!(eval(&p, M31((28 * index + j + 1) as u32)), M31::ZERO);
        }
    }
    assert!(28 * outside < (field::P as usize));
    println!("PASS 66 deterministic symbol-boundary polynomial instances; product formula gives {} disjoint roots",28*outside);
}
