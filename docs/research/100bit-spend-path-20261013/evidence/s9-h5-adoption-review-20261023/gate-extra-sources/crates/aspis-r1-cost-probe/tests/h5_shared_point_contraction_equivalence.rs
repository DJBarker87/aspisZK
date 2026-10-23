//! Differential check for the isolated S2 shared-point-contraction candidate.
//! This compares the retained and candidate `weights.rs` implementations; it
//! does not alter or replace the library's live module.

extern crate alloc;

mod fast_pairing {
    pub use aspis_r1_cost_probe::fast_pairing::*;
}
mod transport {
    pub use aspis_r1_cost_probe::transport::{Variant, TAU};
}
mod verifier {
    pub use aspis_r1_cost_probe::verifier::Error;
}
mod trace {
    pub use aspis_r1_cost_probe::trace::value;
}

#[path = "../../../tools/r1-shared-point-candidate/weights.baseline.rs"]
mod baseline;
mod candidate { pub use aspis_r1_cost_probe::weights::*; }

use aspis_core::{
    circle::SecureCirclePoint,
    field::{WideExact as E, CM31, M31, P, QM31},
};
use aspis_r1_cost_probe::{transport::Variant, verifier::Error};

fn next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut value = *state;
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn random_k(state: &mut u64) -> QM31 {
    let scalar = |state: &mut u64| M31((next(state) % u64::from(P)) as u32);
    QM31 {
        c0: CM31 {
            a: scalar(state),
            b: scalar(state),
        },
        c1: CM31 {
            a: scalar(state),
            b: scalar(state),
        },
    }
}

fn random_e(state: &mut u64) -> E {
    E::new(random_k(state), random_k(state))
}

fn boundary_k() -> QM31 {
    let scalar = M31(P - 1);
    QM31 {
        c0: CM31 {
            a: scalar,
            b: scalar,
        },
        c1: CM31 {
            a: scalar,
            b: scalar,
        },
    }
}

fn categories(state: &mut u64) -> [E; 4] {
    [
        E::ZERO,
        E::ONE,
        E::new(boundary_k(), boundary_k()),
        random_e(state),
    ]
}

fn coefficients(state: &mut u64, len: usize, mode: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(len * E::BYTE_LEN);
    for _ in 0..len {
        let value = match mode {
            0 => E::ZERO,
            1 => E::ONE,
            2 => E::new(boundary_k(), boundary_k()),
            _ => random_e(state),
        };
        out.extend_from_slice(&value.to_le_bytes());
    }
    out
}

fn assert_pair_equal(
    old: &baseline::Weights,
    new: &candidate::Weights,
    alpha: &[E],
    bytes: &[u8],
    kappa: E,
) {
    let old_result = old.pair(alpha, bytes, kappa);
    let new_result = new.pair(alpha, bytes, kappa);
    assert_eq!(new_result, old_result);
}

fn candidate_copy(weights: &baseline::Weights) -> candidate::Weights {
    candidate::Weights {
        variant: weights.variant,
        factors: weights.factors,
        points: weights.points,
        extra: weights.extra,
    }
}

fn random_factors(state: &mut u64) -> [[[QM31; 4]; 5]; 5] {
    core::array::from_fn(|_| core::array::from_fn(|_| core::array::from_fn(|_| random_k(state))))
}

fn shared_guard(weights: &baseline::Weights) -> bool {
    weights.variant == Variant::S2
        && weights.variant.folds() == 2
        && weights.factors[0][2] == weights.factors[2][2]
        && weights.factors[0][3] == weights.factors[2][3]
}

fn scalar_factor(factors: &[QM31; 4], powers: &[E; 4]) -> E {
    (0..4)
        .fold(E::ZERO, |sum, slot| {
            sum.add(powers[baseline::PERM[slot]].mul_qm31(factors[slot]))
        })
        .mul_m31(baseline::QUARTER)
}

#[test]
fn shared_point_contraction_matches_retained_pair() {
    let mut state = 0x243f_6a88_85a3_08d3;
    let mut cases = 0usize;

    // S2 uses two fold challenges and final_len() == 64. Cover zero, unit,
    // canonical boundary, and seeded random challenge/point/coefficient data.
    for case in 0..16 {
        let alpha_k: [QM31; 10] = core::array::from_fn(|i| match (case + i) % 4 {
            0 => QM31::ZERO,
            1 => QM31::ONE,
            2 => boundary_k(),
            _ => random_k(&mut state),
        });
        let z: [SecureCirclePoint; 2] = core::array::from_fn(|i| {
            let pick = |offset: usize, state: &mut u64| match (case + i + offset) % 4 {
                0 => QM31::ZERO,
                1 => QM31::ONE,
                2 => boundary_k(),
                _ => random_k(state),
            };
            SecureCirclePoint {
                x: pick(0, &mut state),
                y: pick(1, &mut state),
            }
        });
        let old = baseline::Weights::new(Variant::S2, &alpha_k, &z).unwrap();
        assert!(
            shared_guard(&old),
            "constructed S2 weights should share the high factors"
        );
        let new = candidate_copy(&old);
        let fold_values = categories(&mut state);
        let kappa_values = categories(&mut state);
        let f = coefficients(&mut state, Variant::S2.final_len(), case % 4);
        for j in 0..4 {
            let alpha = [fold_values[j], fold_values[(j + case) % 4]];
            assert_pair_equal(&old, &new, &alpha, &f, kappa_values[(j + case) % 4]);
            cases += 1;
        }
    }

    // Directly exercise the equality guard on public factor fields. Equal
    // all-zero, all-two, and seeded-random low tensors enter the shared path;
    // a one-cell mismatch must retain the old per-row computation.
    let points = [[QM31::ZERO; 10]; 3];
    let extra = [QM31::ONE, boundary_k()];
    let alpha = [E::new(boundary_k(), QM31::ONE), E::ZERO];
    let kappa = E::new(QM31::ONE, boundary_k());
    let f = coefficients(&mut state, Variant::S2.final_len(), 3);
    for mode in 0..4 {
        let mut factors = random_factors(&mut state);
        if mode < 3 {
            let low = match mode {
                0 => [QM31::ZERO; 4],
                1 => [QM31::ONE.add(QM31::ONE); 4],
                _ => core::array::from_fn(|_| random_k(&mut state)),
            };
            factors[0][2] = low;
            factors[0][3] = low;
            factors[2][2] = low;
            factors[2][3] = low;
            if mode == 2 {
                // With zero fold challenges, ap0=ap1=[1,0,0,0]. These
                // canonical factors produce distinct nonzero scales 1/16
                // and 6/16 for point rows 0 and 2.
                let two = QM31::from_cm31(CM31::new(M31(2), M31::ZERO));
                let three = QM31::from_cm31(CM31::new(M31(3), M31::ZERO));
                factors[0][0] = [QM31::ONE; 4];
                factors[0][1] = [QM31::ONE; 4];
                factors[2][0] = [two; 4];
                factors[2][1] = [three; 4];
            }
        } else {
            factors[0][2] = [QM31::ZERO; 4];
            factors[0][3] = [QM31::ZERO; 4];
            factors[2][2] = [QM31::ZERO; 4];
            factors[2][3] = [QM31::ZERO; 4];
            factors[2][3][0] = QM31::ONE;
        }
        let old = baseline::Weights {
            variant: Variant::S2,
            factors,
            points,
            extra,
        };
        assert_eq!(shared_guard(&old), mode < 3, "manual guard case {mode}");
        if mode == 2 {
            assert_ne!(old.factors[0][0], old.factors[2][0]);
            assert_ne!(old.factors[0][1], old.factors[2][1]);
            let zero = E::ZERO;
            let ap0 = baseline::powers::<4>(zero);
            let ap1 = baseline::powers::<4>(zero);
            assert_eq!(ap0, [E::ONE, E::ZERO, E::ZERO, E::ZERO]);
            assert_eq!(ap1, [E::ONE, E::ZERO, E::ZERO, E::ZERO]);
            let scale0 = scalar_factor(&old.factors[0][0], &ap0)
                .mul(scalar_factor(&old.factors[0][1], &ap1));
            let scale2 = scalar_factor(&old.factors[2][0], &ap0)
                .mul(scalar_factor(&old.factors[2][1], &ap1));
            let six_sixteenths = M31(6).mul(baseline::QUARTER.mul(baseline::QUARTER));
            let one_sixteenth = baseline::QUARTER.mul(baseline::QUARTER);
            assert_eq!(
                scale0,
                E::from_qm31(QM31::from_cm31(CM31::new(one_sixteenth, M31::ZERO)))
            );
            assert_eq!(
                scale2,
                E::from_qm31(QM31::from_cm31(CM31::new(six_sixteenths, M31::ZERO)))
            );
            assert_ne!(scale0, E::ZERO);
            assert_ne!(scale2, E::ZERO);
            assert_ne!(scale0, scale2);
            assert_ne!(kappa, E::ZERO);
        }
        let new = candidate_copy(&old);
        let mode_alpha = if mode == 2 {
            [E::ZERO, E::ZERO]
        } else {
            alpha
        };
        assert_pair_equal(&old, &new, &mode_alpha, &f, kappa);
        cases += 1;
    }

    // S1 and D do not take the guarded S2 contraction. Compare their valid
    // outputs and the ordinary malformed-length error path as controls.
    for variant in [Variant::S1, Variant::D] {
        let alpha_k = core::array::from_fn(|_| random_k(&mut state));
        let z = core::array::from_fn(|_| SecureCirclePoint {
            x: random_k(&mut state),
            y: random_k(&mut state),
        });
        let old = baseline::Weights::new(variant, &alpha_k, &z).unwrap();
        let new = candidate_copy(&old);
        let fold_values = categories(&mut state);
        let alpha = if variant == Variant::S1 {
            &fold_values[..1]
        } else {
            &fold_values[..2]
        };
        let f = coefficients(&mut state, variant.final_len(), 3);
        let kappa = random_e(&mut state);
        assert_pair_equal(&old, &new, alpha, &f, kappa);
        cases += 1;
        let malformed = &f[..f.len() - E::BYTE_LEN];
        assert_eq!(old.pair(alpha, malformed, kappa), Err(Error::Parse));
        assert_eq!(new.pair(alpha, malformed, kappa), Err(Error::Parse));
        cases += 1;
    }

    assert_eq!(cases, 72);
}
