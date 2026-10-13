use aspis_core::field::{CM31, M31, QM31, WideExact, P};
use aspis_r1_cost_probe::verifier;

#[path = "../src/fast_pairing.rs"]
mod fast_pairing;
#[path = "../src/fast_dots.rs"]
mod fast_dots;

fn next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut value = *state;
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn random_m31(state: &mut u64) -> M31 {
    M31((next(state) % u64::from(P)) as u32)
}

fn random_qm31(state: &mut u64) -> QM31 {
    let mut scalar = || random_m31(state);
    QM31 {
        c0: CM31 { a: scalar(), b: scalar() },
        c1: CM31 { a: scalar(), b: scalar() },
    }
}

fn write_qm31(bytes: &mut [u8], value: QM31) {
    value.write_le_bytes(bytes);
}

fn inputs(state: &mut u64, case: usize) -> (Vec<u8>, [WideExact; 29]) {
    let mut q = vec![0u8; 608];
    for slot in 0..4 {
        for term in 0..26 {
            let value = match case % 4 {
                0 => M31::ZERO,
                1 => M31::ONE,
                2 => M31(P - 1),
                _ => random_m31(state),
            };
            let offset = slot * 120 + term * 4;
            q[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
        }
        let key = match case % 4 {
            0 => QM31::ZERO,
            1 => QM31::ONE,
            2 => QM31 {
                c0: CM31 { a: M31(P - 1), b: M31(P - 1) },
                c1: CM31 { a: M31(P - 1), b: M31(P - 1) },
            },
            _ => random_qm31(state),
        };
        write_qm31(&mut q[slot * 120 + 104..slot * 120 + 120], key);
        for term in 0..2 {
            let value = match case % 4 {
                0 => QM31::ZERO,
                1 => QM31::ONE,
                2 => QM31 {
                    c0: CM31 { a: M31(P - 1), b: M31(P - 1) },
                    c1: CM31 { a: M31(P - 1), b: M31(P - 1) },
                },
                _ => random_qm31(state),
            };
            let offset = 480 + slot * 32 + term * 16;
            write_qm31(&mut q[offset..offset + 16], value);
        }
    }

    let high = || WideExact::from_limbs([P - 1; 8]).unwrap();
    let g = core::array::from_fn(|_| match case % 4 {
        0 => WideExact::ZERO,
        1 => WideExact::ONE,
        2 => high(),
        _ => WideExact::from_limbs(core::array::from_fn(|_| random_m31(state).0)).unwrap(),
    });
    (q, g)
}

#[test]
fn batched_dots_match_the_frozen_verifier() {
    let mut state = 0x1319_8a2e_0370_7344;
    for case in 0..4096 {
        let (q, g) = inputs(&mut state, case);
        assert_eq!(fast_dots::four_dots(&q, &g), verifier::four_dots(&q, &g), "case {case}");
    }
}

#[test]
fn batched_dots_preserve_noncanonical_input_panics() {
    let mut state = 0x082e_fa98_ec4e_6c89;
    let (mut q, g) = inputs(&mut state, 3);
    q[0..4].copy_from_slice(&P.to_le_bytes());
    assert!(std::panic::catch_unwind(|| fast_dots::four_dots(&q, &g)).is_err());
    assert!(std::panic::catch_unwind(|| verifier::four_dots(&q, &g)).is_err());

    let (mut q, g) = inputs(&mut state, 3);
    q[104..108].copy_from_slice(&P.to_le_bytes());
    assert!(std::panic::catch_unwind(|| fast_dots::four_dots(&q, &g)).is_err());
    assert!(std::panic::catch_unwind(|| verifier::four_dots(&q, &g)).is_err());
}
