use aspis_core::field::{CM31, M31, QM31, WideExact as E, P};

#[path = "../src/fast_pairing.rs"]
mod fast_pairing;

use fast_pairing::{EbyEDot, EbyKDot};

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

fn random_e(state: &mut u64) -> E {
    E::new(random_qm31(state), random_qm31(state))
}

fn edge_e(mode: usize) -> E {
    match mode {
        0 => E::ZERO,
        1 => E::ONE,
        _ => E::from_limbs([P - 1; 8]).unwrap(),
    }
}

fn edge_k(mode: usize) -> QM31 {
    match mode {
        0 => QM31::ZERO,
        1 => QM31::ONE,
        _ => QM31 {
            c0: CM31 { a: M31(P - 1), b: M31(P - 1) },
            c1: CM31 { a: M31(P - 1), b: M31(P - 1) },
        },
    }
}

fn check_length(len: usize, mode: usize, state: &mut u64) {
    let (left, right, scalar): (Vec<E>, Vec<E>, Vec<QM31>) = (0..len)
        .map(|_| {
            if mode < 3 {
                (edge_e(mode), edge_e(mode), edge_k(mode))
            } else {
                (random_e(state), random_e(state), random_qm31(state))
            }
        })
        .fold((Vec::new(), Vec::new(), Vec::new()), |mut values, (a, b, k)| {
            values.0.push(a);
            values.1.push(b);
            values.2.push(k);
            values
        });

    let mut expected_k = E::ZERO;
    let mut actual_k = EbyKDot::new();
    let mut expected_e = E::ZERO;
    let mut actual_e = EbyEDot::new();
    for i in 0..len {
        expected_k = expected_k.add(left[i].mul_qm31(scalar[i]));
        actual_k.push(left[i], scalar[i]).unwrap();
        expected_e = expected_e.add(left[i].mul(right[i]));
        actual_e.push(left[i], right[i]).unwrap();
    }
    assert_eq!(actual_k.finish(), expected_k, "E-by-K len {len}, mode {mode}");
    assert_eq!(actual_e.finish(), expected_e, "E-by-E len {len}, mode {mode}");
}

#[test]
fn dot_accumulators_match_core_products_at_boundary_lengths() {
    let mut state = 0x6a09_e667_f3bc_c909;
    for len in [0, 1, 3, 4, 16, 29, 64, 256, 4096] {
        for mode in 0..4 {
            check_length(len, mode, &mut state);
        }
    }
}

#[test]
fn dot_accumulators_reject_noncanonical_scalars_and_excess_terms() {
    let invalid = QM31 {
        c0: CM31 { a: M31(P), b: M31::ZERO },
        c1: CM31::ZERO,
    };
    let mut by_k = EbyKDot::new();
    assert_eq!(by_k.push(E::ONE, invalid), Err(()));
    by_k.push(E::ONE, QM31::ONE).unwrap();
    assert_eq!(by_k.finish(), E::ONE);

    let mut by_e = EbyEDot::new();
    by_e.push(E::ONE, E::ONE).unwrap();
    assert_eq!(by_e.finish(), E::ONE);

    let mut by_k = EbyKDot::new();
    let mut by_e = EbyEDot::new();
    for _ in 0..4096 {
        by_k.push(E::ZERO, QM31::ZERO).unwrap();
        by_e.push(E::ZERO, E::ZERO).unwrap();
    }
    assert_eq!(by_k.push(E::ZERO, QM31::ZERO), Err(()));
    assert_eq!(by_e.push(E::ZERO, E::ZERO), Err(()));
    assert_eq!(by_k.finish(), E::ZERO);
    assert_eq!(by_e.finish(), E::ZERO);
}
