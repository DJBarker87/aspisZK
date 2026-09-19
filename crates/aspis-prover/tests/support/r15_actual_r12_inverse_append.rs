//! R15: apply the retained R12 inverse to the actual selected terminal.
//!
//! The transcript entry is the same named diagnostic public prefix as R14.
//! This proves no C2-root or generated-q22 correspondence.

use super::*;
use aspis_core::{
    state_only_hiding::begin_state_only_masked_sumcheck,
    transcript::{label, Transcript},
};
use aspis_prover::state_only_hiding::state_only_initial_mask_claim;
use aspis_statement::pool_v1::build_pool_v1_pair_forest_copy_helper_v1;
use sha2::{Digest as ShaDigest, Sha256};

#[path = "r12_data.rs"]
mod r12_data;

fn r15_hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for part in parts {
        h.update(part);
    }
    h.finalize().into()
}

fn r15_matrix_inverse(mut matrix: Vec<Vec<QM31>>) -> Vec<Vec<QM31>> {
    let n = matrix.len();
    let mut inverse = vec![vec![QM31::ZERO; n]; n];
    for i in 0..n {
        inverse[i][i] = QM31::ONE;
    }
    for pivot in 0..n {
        let row = (pivot..n)
            .find(|&row| matrix[row][pivot] != QM31::ZERO)
            .expect("R12 fixed inverse");
        matrix.swap(pivot, row);
        inverse.swap(pivot, row);
        let scale = matrix[pivot][pivot].inv();
        for column in 0..n {
            matrix[pivot][column] = matrix[pivot][column].mul(scale);
            inverse[pivot][column] = inverse[pivot][column].mul(scale);
        }
        let matrix_row = matrix[pivot].clone();
        let inverse_row = inverse[pivot].clone();
        for row in 0..n {
            if row == pivot {
                continue;
            }
            let factor = matrix[row][pivot];
            for column in 0..n {
                matrix[row][column] = matrix[row][column].sub(factor.mul(matrix_row[column]));
                inverse[row][column] = inverse[row][column].sub(factor.mul(inverse_row[column]));
            }
        }
    }
    inverse
}

fn r15_matvec(matrix: &[Vec<QM31>], vector: &[QM31]) -> Vec<QM31> {
    matrix
        .iter()
        .map(|row| {
            row.iter()
                .zip(vector)
                .fold(QM31::ZERO, |sum, (a, b)| sum.add(a.mul(*b)))
        })
        .collect()
}

fn r15_eval(coefficients: &[QM31], x: QM31) -> QM31 {
    coefficients
        .iter()
        .rev()
        .fold(QM31::ZERO, |value, coefficient| {
            value.mul(x).add(*coefficient)
        })
}

fn r15_interpolate(values: &[QM31]) -> Vec<QM31> {
    let mut answer = vec![QM31::ZERO; values.len()];
    for i in 0..values.len() {
        let mut basis = vec![QM31::ONE];
        for j in 0..values.len() {
            if i == j {
                continue;
            }
            let xj = lift(j as u32);
            let scale = lift(i as u32).sub(xj).inv();
            let mut next = vec![QM31::ZERO; basis.len() + 1];
            for k in 0..basis.len() {
                next[k] = next[k].sub(basis[k].mul(xj));
                next[k + 1] = next[k + 1].add(basis[k]);
            }
            basis = next.into_iter().map(|value| value.mul(scale)).collect();
        }
        for (coefficient, basis_coefficient) in answer.iter_mut().zip(basis) {
            *coefficient = coefficient.add(values[i].mul(basis_coefficient));
        }
    }
    answer
}

fn r15_compact(coefficients: &[QM31]) -> Vec<QM31> {
    core::iter::once(coefficients[0])
        .chain(coefficients[2..28].iter().copied())
        .collect()
}

fn r15_translate(coefficients: &[QM31], shift: QM31) -> Vec<QM31> {
    r15_interpolate(
        &(0..coefficients.len())
            .map(|x| r15_eval(coefficients, lift(x as u32).add(shift)))
            .collect::<Vec<_>>(),
    )
}

fn r15_weight(index: usize) -> u32 {
    275 + 150 * index as u32
}

fn r15_at(prefix: &[QM31], t: QM31, suffix: usize) -> [QM31; 10] {
    let cut = prefix.len();
    let mut point = [QM31::ZERO; 10];
    point[..cut].copy_from_slice(prefix);
    point[cut] = t;
    for coordinate in cut + 1..10 {
        point[coordinate] = lift(((suffix >> (9 - coordinate)) & 1) as u32);
    }
    point
}

fn r15_fixed_inverses(cut: usize, shifts: &[u32; 27]) -> (Vec<Vec<QM31>>, Vec<Vec<QM31>>) {
    let mut boundary = vec![vec![QM31::ZERO; 27]; 27];
    for column in 0..27 {
        let values = (0..28)
            .map(|x| {
                let x = lift(x);
                QM31::ONE
                    .sub(x)
                    .mul(x.pow(column as u64))
                    .sub(x.mul(x.sub(QM31::ONE).pow(column as u64)))
            })
            .collect::<Vec<_>>();
        for (row, value) in r15_compact(&r15_interpolate(&values))
            .into_iter()
            .enumerate()
        {
            boundary[row][column] = value;
        }
    }
    let weight = lift(r15_weight(cut));
    let mut moments = vec![vec![QM31::ZERO; 27]; 27];
    for (column, &shift) in shifts.iter().enumerate() {
        let values = (0..27)
            .map(|x| QM31::ONE.add(weight.mul(lift(x)).add(lift(shift)).pow(26)))
            .collect::<Vec<_>>();
        for (row, value) in r15_interpolate(&values).into_iter().enumerate() {
            moments[row][column] = value;
        }
    }
    (r15_matrix_inverse(boundary), r15_matrix_inverse(moments))
}

fn r15_lift_target(
    cut: usize,
    prefix: &[QM31],
    pairs: &[Vec<[usize; 2]>],
    boundary_inverse: &[Vec<QM31>],
    moment_inverse: &[Vec<QM31>],
    sent: &[QM31],
) -> [QM31; ROWS] {
    let boundary = r15_matvec(boundary_inverse, sent);
    let prefix_shift = prefix
        .iter()
        .enumerate()
        .fold(QM31::ZERO, |sum, (i, value)| {
            sum.add(lift(r15_weight(i)).mul(*value))
        });
    let translated = r15_translate(
        &boundary,
        prefix_shift.mul(lift(r15_weight(cut)).inv()).neg(),
    );
    let coefficients = r15_matvec(moment_inverse, &translated);
    let mut delta = [QM31::ZERO; ROWS];
    for (coefficient, family) in coefficients.into_iter().zip(pairs) {
        for [left, right] in family {
            delta[*left] = delta[*left].add(coefficient);
            delta[*right] = delta[*right].sub(coefficient);
        }
    }
    delta
}

fn r15_claims(
    c1: &[Vec<M31>; 16],
    helper: &[QM31; ROWS],
    g: &[QM31; ROWS],
    point: &[QM31; 10],
) -> [QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1] {
    let mut output = claims(c1, helper, point);
    for (index, opening) in [*point, successor_point(point), xor12_point(point)]
        .iter()
        .enumerate()
    {
        output[index * 28 + 27] = multilinear_evaluate_qm31(g, opening).unwrap();
    }
    output
}

#[test]
fn r15_r12_inverse_hits_arbitrary_compact_targets_at_actual_selected_terminal() {
    let pool = [0x31; 32];
    let domain = [0x73; 32];
    let prepared = prepare_v7_pair_forest_transfer_fixture_v1(
        pool,
        [0x32; 32],
        [0x33; 32],
        0,
        domain,
        source_snapshot(pool, domain),
    )
    .unwrap();
    let context = PoolV1PaymentRelationContextV1 {
        runtime_binding: PoolV1PaymentRuntimeBindingV1 {
            pool: prepared.public.pool,
            deployment_domain: prepared.public.deployment_domain,
            anchor_sequence: prepared.public.anchor_sequence,
            anchor_root: prepared.public.anchor_root,
            asset_id: prepared.public.asset_id,
        },
        spent_nullifiers: &[],
    };
    let compiled = compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(
        &prepared.public,
        &prepared.witness,
        context,
        prepared.transition.live_snapshot,
    )
    .unwrap();
    let lambda = lift(19);
    let chi = lift(23);
    let theta = lift(29);
    let mu = lift(31);
    let zero_point = core::array::from_fn(|i| lift(41 + i as u32));
    let helper: [QM31; ROWS] = build_pool_v1_pair_forest_copy_helper_v1(
        &compiled.trace,
        compiled.public_statement.live_snapshot.next_pair_index,
        lambda,
        chi,
    )
    .unwrap()
    .try_into()
    .unwrap();
    let zero = [QM31::ZERO; ROWS];
    let masks: [Vec<M31>; 10] = core::array::from_fn(|_| vec![M31::ZERO; ROWS]);
    let initial = state_only_initial_mask_claim(&compiled.semantic_c1, &masks, &zero).unwrap();
    let mut transcript = Transcript::new(r15_hash);
    transcript.absorb(label::STATEMENT, b"R14-actual-terminal-offset-fixture");
    let eta = begin_state_only_masked_sumcheck(&mut transcript, initial).unwrap();

    let terminal_values = |g: &[QM31; ROWS], prefix: &[QM31]| {
        (0..28)
            .map(|sample| {
                let t = lift(sample as u32);
                (0..(1usize << (9 - prefix.len()))).fold(QM31::ZERO, |sum, suffix| {
                    let point = r15_at(prefix, t, suffix);
                    sum.add(
                        evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(
                            &prepared.public,
                            &compiled.public_statement,
                            &r15_claims(&compiled.semantic_c1.c1, &helper, g, &point),
                            &point,
                            lambda,
                            chi,
                            theta,
                            &zero_point,
                            mu,
                            eta,
                        )
                        .unwrap(),
                    )
                })
            })
            .collect::<Vec<_>>()
    };

    let mut prefix = Vec::new();
    let mut boundary = initial;
    for round in 0..2 {
        let values = terminal_values(&zero, &prefix);
        assert_eq!(values[0].add(values[1]), boundary);
        let polynomial = r15_interpolate(&values);
        let mut frame = Vec::with_capacity(433);
        frame.push(round as u8);
        for coefficient in core::iter::once(0).chain(2..28) {
            let mut bytes = [0u8; 16];
            polynomial[coefficient].write_le_bytes(&mut bytes);
            frame.extend_from_slice(&bytes);
        }
        transcript.absorb(label::V6_COMPACT_SEMANTIC_ROUND, &frame);
        let challenge = transcript.challenge_qm31().unwrap();
        boundary = r15_eval(&polynomial, challenge);
        prefix.push(challenge);
    }

    let extension = QM31 {
        c0: CM31::new(M31(2), M31(3)),
        c1: CM31::new(M31(5), M31(7)),
    };
    for (cut, pairs, shifts) in [
        (
            1usize,
            r12_data::PAIRS_R1
                .iter()
                .map(|family| family.to_vec())
                .collect::<Vec<Vec<[usize; 2]>>>(),
            &r12_data::SHIFTS_R1,
        ),
        (
            2usize,
            r12_data::PAIRS_R2
                .iter()
                .map(|family| family.to_vec())
                .collect::<Vec<Vec<[usize; 2]>>>(),
            &r12_data::SHIFTS_R2,
        ),
    ] {
        let (boundary_inverse, moment_inverse) = r15_fixed_inverses(cut, shifts);
        let basis = (0..27)
            .map(|i| if i == 8 { extension } else { QM31::ZERO })
            .collect::<Vec<_>>();
        let arbitrary = (0..27)
            .map(|i| extension.mul(lift((3 * i + 7) as u32)))
            .collect::<Vec<_>>();
        for target in [basis, arbitrary] {
            let delta = r15_lift_target(
                cut,
                &prefix[..cut],
                &pairs,
                &boundary_inverse,
                &moment_inverse,
                &target,
            );
            assert_eq!(
                state_only_initial_mask_claim(&compiled.semantic_c1, &masks, &delta).unwrap(),
                initial,
                "R12 pair family must preserve eta's actual initial claim"
            );
            for earlier in 0..cut {
                let delta_values = terminal_values(&delta, &prefix[..earlier]);
                let zero_values = terminal_values(&zero, &prefix[..earlier]);
                assert!(
                    delta_values
                        .iter()
                        .zip(zero_values)
                        .all(|(left, right)| *left == right),
                    "R12 correction changed an earlier actual selected-terminal round"
                );
            }
            let delta_values = terminal_values(&delta, &prefix[..cut]);
            let zero_values = terminal_values(&zero, &prefix[..cut]);
            let difference = delta_values
                .iter()
                .zip(zero_values)
                .map(|(left, right)| left.sub(right))
                .collect::<Vec<_>>();
            assert_eq!(r15_compact(&r15_interpolate(&difference)), target);
        }
    }
}
