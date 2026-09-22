//! Standalone actual-QM31 differential for the R20 whole-dot candidate.
//! Enable with `--cfg r20_whole_dot_check`; this is not a protocol gate.
extern crate aspis_core as corelib;
#[path = "r20_whole_dot.rs"]
mod r20_whole_dot;
#[path = "r20_private_dot_adapter.rs"]
mod r20_private_dot_adapter;
#[path = "r20_semantic_basis.rs"]
mod r20_semantic_basis;

use corelib::field::{PreparedQm31Multiplier, CM31, M31, P, QM31};
use r20_whole_dot::{dot, Dot, Error, MAX_TERMS};

fn q(n: u64) -> QM31 {
    let x = |k: u64| M31((k % u64::from(P)) as u32);
    QM31 {
        c0: CM31::new(x(n), x(n * 3 + 1)),
        c1: CM31::new(x(n * 5 + 2), x(n * 7 + 3)),
    }
}

fn maximal(n: usize) -> QM31 {
    let p = P - 1;
    if n & 1 == 0 {
        QM31 {
            c0: CM31::new(M31(p), M31(p - 1)),
            c1: CM31::new(M31(p - 2), M31(p - 3)),
        }
    } else {
        QM31 {
            c0: CM31::new(M31(p - 3), M31(p - 2)),
            c1: CM31::new(M31(p - 1), M31(p)),
        }
    }
}

fn all_max() -> QM31 {
    let p = P - 1;
    QM31 {
        c0: CM31::new(M31(p), M31(p)),
        c1: CM31::new(M31(p), M31(p)),
    }
}

fn scalar(left: &[QM31], right: &[QM31]) -> QM31 {
    left.iter()
        .zip(right)
        .fold(QM31::ZERO, |s, (&a, &b)| s.add(a.mul(b)))
}

fn prepared3(left: &[QM31], right: &[QM31]) -> QM31 {
    let l: [PreparedQm31Multiplier; 3] =
        core::array::from_fn(|i| PreparedQm31Multiplier::new(left[i]));
    corelib::field::qm31_sum_products3_prepared(&l, right[..3].try_into().unwrap())
}

fn control_vector(n: usize, case: usize, side: u64) -> Vec<QM31> {
    if case == 0 {
        return vec![all_max(); n];
    }
    (0..n)
        .map(|i| {
            if (i + case + side as usize) % 11 == 0 {
                maximal(i + case + side as usize)
            } else {
                q((i + 1 + case * 101 + side as usize * 1009) as u64)
            }
        })
        .collect()
}

#[cfg(r20_whole_dot_check)]
fn main() {
    r20_semantic_basis::differential_check(|a,b|dot(a,b).unwrap());
    assert_eq!(MAX_TERMS, 4096);
    let lengths = [
        0usize, 1, 2, 3, 4, 5, 6, 7, 15, 16, 17, 27, 163, 271, 4095, 4096,
    ];
    let mut vectors = 0usize;
    for &n in &lengths {
        for case in 0..32usize {
            let left = control_vector(n, case, 0);
            let right = control_vector(n, case, 1);
            let whole = dot(&left, &right).unwrap();
            assert_eq!(r20_private_dot_adapter::dot(&left,&right).unwrap(),whole,"private packed arithmetic case {case} length {n}");
            assert_eq!(
                whole,
                scalar(&left, &right),
                "scalar case {case} length {n}"
            );
            if n == 3 {
                assert_eq!(whole, prepared3(&left, &right), "prepared-3 case {case}");
            }
            if n == 4 {
                let l: [QM31; 4] = left[..4].try_into().unwrap();
                let r: [QM31; 4] = right[..4].try_into().unwrap();
                assert_eq!(
                    whole,
                    corelib::field::qm31_sum_products4(l, r),
                    "four-product case {case}"
                );
            }
            vectors += 1;
        }
    }
    for side in 0..2 {
        for limb in 0..4 {
            let mut bad = QM31::ONE;
            match (side, limb) {
                (0, 0) => bad.c0.a = M31(P),
                (0, 1) => bad.c0.b = M31(P),
                (0, 2) => bad.c1.a = M31(P),
                (0, 3) => bad.c1.b = M31(P),
                (1, 0) => bad.c0.a = M31(P),
                (1, 1) => bad.c0.b = M31(P),
                (1, 2) => bad.c1.a = M31(P),
                (1, 3) => bad.c1.b = M31(P),
                _ => unreachable!(),
            }
            let left = if side == 0 {
                vec![bad]
            } else {
                vec![QM31::ONE]
            };
            let right = if side == 0 {
                vec![QM31::ONE]
            } else {
                vec![bad]
            };
            let pair = (&left[..], &right[..]);
            assert!(r20_private_dot_adapter::dot(pair.0,pair.1).is_none());
            assert!(
                matches!(dot(pair.0, pair.1), Err(Error::NonCanonical)),
                "noncanonical side {side} limb {limb}"
            );
        }
    }
    assert!(matches!(dot(&[QM31::ONE], &[]), Err(Error::Length)));
    let too_long = vec![QM31::ONE; MAX_TERMS + 1];
    assert!(matches!(dot(&too_long, &too_long), Err(Error::TooLong)));
    let mut direct = Dot::new();
    for _ in 0..MAX_TERMS {
        direct.push_canonical(QM31::ONE, QM31::ONE).unwrap();
    }
    assert_eq!(direct.finish(), QM31::from_cm31(CM31::new(M31((MAX_TERMS as u32) % P), M31::ZERO)));
    let mut over = Dot::new();
    for i in 0..=MAX_TERMS {
        if i == MAX_TERMS {
            assert!(over.push_canonical(QM31::ONE, QM31::ONE).is_err());
        } else {
            over.push_canonical(QM31::ONE, QM31::ONE).unwrap();
        }
    }
    println!("{{\"all_passed\":true,\"vectors\":{vectors},\"lengths\":[0,1,2,3,4,5,6,7,15,16,17,27,163,271,4095,4096],\"prepared_controls\":[3],\"staged_controls\":[4],\"maximal_canonical_limbs\":true,\"noncanonical_limb_controls\":8,\"direct_bound_controls\":true,\"canonicality_checked_once\":true,\"protocol_claim\":false}}");
}

#[cfg(not(r20_whole_dot_check))]
fn main() {
    panic!("compile this standalone checker with --cfg r20_whole_dot_check");
}
