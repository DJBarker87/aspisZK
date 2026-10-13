use aspis_core::{
    circle::SecureCirclePoint,
    field::{CM31, M31, QM31, WideExact as E, P},
};
use aspis_r1_cost_probe::{transport::Variant, weights::{field, powers, Weights}};

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
        c0: CM31 { a: scalar(state), b: scalar(state) },
        c1: CM31 { a: scalar(state), b: scalar(state) },
    }
}

fn random_e(state: &mut u64) -> E {
    E::new(random_k(state), random_k(state))
}

fn reference_pair(weights: &Weights, alpha: &[E], bytes: &[u8], kappa: E) -> E {
    let challenge = powers::<7>(kappa);
    let mut result = E::ZERO;
    for (kind, &kind_challenge) in challenge.iter().enumerate() {
        let mut part = E::ZERO;
        for j in 0..weights.variant.final_len() {
            part = part.add(field(bytes, j).mul(weights.dual_raw(kind, j, alpha)));
        }
        result = result.add(kind_challenge.mul(part));
    }
    result
}

#[test]
fn optimized_pair_matches_raw_dual_expression_for_all_variants() {
    let mut state = 0x243f_6a88_85a3_08d3;
    let high = QM31 {
        c0: CM31 { a: M31(P - 1), b: M31(P - 2) },
        c1: CM31 { a: M31(P - 3), b: M31(P - 4) },
    };

    for variant in [Variant::S1, Variant::S2, Variant::D] {
        for case in 0..8 {
            let mut alpha_k: [QM31; 10] = core::array::from_fn(|_| random_k(&mut state));
            let z: [SecureCirclePoint; 2] = core::array::from_fn(|_| SecureCirclePoint {
                x: random_k(&mut state),
                y: random_k(&mut state),
            });
            let alpha_pair: [E; 2] = match case % 4 {
                0 => [E::ZERO, E::ZERO],
                1 => [E::ONE, E::ONE],
                2 => [E::new(high, high), E::new(high, high)],
                _ => [random_e(&mut state), random_e(&mut state)],
            };
            let weights = Weights::new(variant, &alpha_k, &z).unwrap();
            let alpha = if variant == Variant::S1 {
                vec![alpha_pair[0]]
            } else {
                vec![alpha_pair[0], alpha_pair[1]]
            };
            let mut bytes = vec![0u8; variant.final_len() * E::BYTE_LEN];
            for block in bytes.chunks_exact_mut(E::BYTE_LEN) {
                block.copy_from_slice(&random_e(&mut state).to_le_bytes());
            }
            let kappa = match case % 4 {
                0 => E::ZERO,
                1 => E::ONE,
                2 => E::new(high, high),
                _ => random_e(&mut state),
            };
            let expected = reference_pair(&weights, &alpha, &bytes, kappa);
            let actual = weights.pair(&alpha, &bytes, kappa).unwrap();
            assert_eq!(actual, expected, "variant {variant:?}, case {case}");
        }
    }
}
