//! R10 research-only semantic H1 cut over a deterministic compiler fixture.
//!
//! This is deliberately an integration test: it does not enter the prover or
//! any production protocol path, and it emits no witness material.  The only
//! fixture is the feature-gated, deterministic host fixture.

use aspis_core::field::{CM31, M31, QM31};
use aspis_prover::v7_pair_forest_fixture::prepare_v7_pair_forest_transfer_fixture_v1;
use aspis_statement::{
    constraints_v4::{multilinear_evaluate, multilinear_evaluate_qm31},
    pool_v1::{
        compile_pool_v1_pair_forest_private_transfer_merged_c1_v1,
        pool_v1_empty_roots, pool_v1_tree_parent, PoolV1PairLiveSnapshotV1,
        PoolV1PaymentRelationContextV1, PoolV1PaymentRuntimeBindingV1,
        POOL_V1_PAIR_TREE_DEPTH,
    },
    pool_v1::pair_forest_copy_terminal::{
        evaluate_pool_v1_pair_forest_copy_terminal_compiled_v1,
        pool_v1_pair_forest_copy_active_row_masks_compiled_v1,
        PoolV1PairForestCompiledVariantV1,
    },
    pool_v1::pair_forest_semantic_terminal::{
        evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1,
        POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1,
    },
    poseidon2::Digest,
    state_only_poseidon::{successor_point, xor12_point},
};

const SAMPLES: usize = 28;
const ROWS: usize = 1024;

fn lift(value: u32) -> QM31 {
    QM31::from_cm31(CM31::from_m31(M31(value)))
}

fn point(t: QM31, b: usize) -> [QM31; 10] {
    let mut point = [QM31::ZERO; 10];
    point[0] = t;
    for offset in 0..9 {
        point[offset + 1] = if (b >> (8 - offset)) & 1 == 0 {
            QM31::ZERO
        } else {
            QM31::ONE
        };
    }
    point
}

fn eq(z: &[QM31; 10], x: &[QM31; 10]) -> QM31 {
    z.iter().zip(x).fold(QM31::ONE, |product, (&a, &b)| {
        let ab = a.mul(b);
        product.mul(QM31::ONE.sub(a).sub(b).add(ab).add(ab))
    })
}

fn openings(c1: &[Vec<M31>; 16], t: QM31, b: usize) -> [QM31; 16] {
    let one_minus_t = QM31::ONE.sub(t);
    core::array::from_fn(|column| {
        one_minus_t
            .mul(lift(c1[column][b].0))
            .add(t.mul(lift(c1[column][b + 512].0)))
    })
}

fn h1_opening(pad: &[QM31; ROWS], t: QM31, b: usize) -> QM31 {
    QM31::ONE
        .sub(t)
        .mul(pad[b])
        .add(t.mul(pad[b + 512]))
}

fn claims(
    c1: &[Vec<M31>; 16],
    h1: &[QM31; ROWS],
    point: &[QM31; 10],
) -> [QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1] {
    // These are the real z, successor(z), xor12(z) opening geometries.  The
    // H1 comparison is fixed-context, but no synthetic three-opening trace is
    // substituted for the selected terminal.
    let mut claims = [QM31::ZERO; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1];
    for (selected_point, opening_point) in [*point, successor_point(point), xor12_point(point)].iter().enumerate() {
        for column in 0..16 {
            claims[selected_point * 28 + column] = multilinear_evaluate(&c1[column], opening_point)
                .expect("compiler C1 shape");
        }
        claims[selected_point * 28 + 26] = multilinear_evaluate_qm31(h1, opening_point)
            .expect("H1 shape");
    }
    claims
}

fn multiply_by_x(poly: &[QM31]) -> Vec<QM31> {
    let mut result = vec![QM31::ZERO; poly.len() + 1];
    result[1..].copy_from_slice(poly);
    result
}

fn interpolate(values: &[QM31]) -> Vec<QM31> {
    let mut answer = vec![QM31::ZERO; values.len()];
    for i in 0..values.len() {
        let mut basis = vec![QM31::ONE];
        for j in 0..values.len() {
            if i == j {
                continue;
            }
            let xj = lift(j as u32);
            let denominator = lift(i as u32).sub(xj).inv();
            let shifted = multiply_by_x(&basis);
            let mut next = vec![QM31::ZERO; basis.len() + 1];
            for k in 0..basis.len() {
                next[k] = next[k].sub(basis[k].mul(xj));
            }
            for k in 0..shifted.len() {
                next[k] = next[k].add(shifted[k]);
            }
            basis = next.into_iter().map(|v| v.mul(denominator)).collect();
        }
        for (coefficient, basis_coefficient) in answer.iter_mut().zip(basis) {
            *coefficient = coefficient.add(values[i].mul(basis_coefficient));
        }
    }
    answer
}

fn evaluate(coefficients: &[QM31], x: QM31) -> QM31 {
    coefficients
        .iter()
        .rev()
        .fold(QM31::ZERO, |value, coefficient| value.mul(x).add(*coefficient))
}

fn source_snapshot(pool: [u8; 32], domain: [u8; 32]) -> PoolV1PairLiveSnapshotV1 {
    let ordinary = pool_v1_empty_roots();
    let roots: [Digest; POOL_V1_PAIR_TREE_DEPTH + 1] = core::array::from_fn(|level| {
        if level < POOL_V1_PAIR_TREE_DEPTH {
            ordinary[level + 1]
        } else {
            pool_v1_tree_parent(&ordinary[POOL_V1_PAIR_TREE_DEPTH], &ordinary[POOL_V1_PAIR_TREE_DEPTH])
        }
    });
    PoolV1PairLiveSnapshotV1 {
        pool,
        deployment_domain: domain,
        sequence: 0,
        next_pair_index: 0,
        current_root: roots[POOL_V1_PAIR_TREE_DEPTH],
        frontier: core::array::from_fn(|level| roots[level]),
    }
}

fn inactive_rows() -> Vec<usize> {
    pool_v1_pair_forest_copy_active_row_masks_compiled_v1()
        .iter()
        .enumerate()
        .flat_map(|(block, mask)| {
            (0..16).filter_map(move |bit| {
                ((*mask >> bit) & 1 == 0).then_some(block * 16 + bit)
            })
        })
        .collect()
}

#[test]
fn r10_real_compiler_h1_cut_matches_complete_selected_terminal() {
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
    .expect("deterministic source-valid fixture");
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
    .expect("compiler-valid C1 fixture");
    assert_eq!(compiled.semantic_c1.c1.len(), 16);
    assert!(compiled.semantic_c1.c1.iter().all(|column| column.len() == ROWS));

    let lambda = lift(19);
    let chi = lift(23);
    let theta = lift(29);
    let mu = lift(31);
    let eta = lift(37);
    let zero_point = core::array::from_fn(|i| lift((41 + i) as u32));
    let inactive = inactive_rows();
    assert!(inactive.len() > 3, "the frozen schedule must expose inactive rows");

    // Matrix samples K(t,b), extracted from the actual public Copy evaluator.
    let mut k_samples = vec![vec![QM31::ZERO; 512]; SAMPLES];
    for (sample, row) in k_samples.iter_mut().enumerate() {
        let t = lift(sample as u32);
        for (b, entry) in row.iter_mut().enumerate() {
            let p = point(t, b);
            let opened = openings(&compiled.semantic_c1.c1, t, b);
            let zero = evaluate_pool_v1_pair_forest_copy_terminal_compiled_v1(
                &opened, QM31::ZERO, &p, lambda, chi,
                compiled.public_statement.live_snapshot.next_pair_index,
                PoolV1PairForestCompiledVariantV1::PrivateTransfer,
            );
            let one = evaluate_pool_v1_pair_forest_copy_terminal_compiled_v1(
                &opened, QM31::ONE, &p, lambda, chi,
                compiled.public_statement.live_snapshot.next_pair_index,
                PoolV1PairForestCompiledVariantV1::PrivateTransfer,
            );
            assert_eq!(zero.active, one.active, "active selector depends only on point");
            *entry = eta.mul(
                eq(&zero_point, &p)
                    .mul(theta.pow(28))
                    .mul(one.residual.sub(zero.residual))
                    .add(mu)
                    .add(mu.mul(mu).mul(QM31::ONE.sub(zero.active))),
            );
        }
    }
    // The 28-node route is the reference extraction.  Independently reduce
    // each source multiplier to coefficients and require the documented
    // degree-10 bound before accepting the 11-node fast route.
    for b in 0..512 {
        let reference: Vec<_> = (0..SAMPLES).map(|sample| k_samples[sample][b]).collect();
        let coefficients = interpolate(&reference);
        assert!(coefficients[11..].iter().all(|coefficient| *coefficient == QM31::ZERO),
            "source Copy multiplier has degree above ten at Boolean suffix {b}");
        assert_eq!(interpolate(&reference[..11]), coefficients[..11],
            "11-node interpolation disagrees with the 28-node source reference at suffix {b}");
    }

    // Three explicit balanced pads in the real fixed inactive block.  Their
    // support remains source-visible here; no hiding claim is made by this test.
    for &target in &[inactive[1], inactive[inactive.len() / 2], *inactive.last().unwrap()] {
        let base = inactive[0];
        let mut pad = [QM31::ZERO; ROWS];
        pad[target] = QM31::ONE;
        pad[base] = QM31::ONE.neg();

        let expected_samples: Vec<_> = (0..SAMPLES)
            .map(|sample| {
                let t = lift(sample as u32);
                (0..512).fold(QM31::ZERO, |sum, b| {
                    sum.add(k_samples[sample][b].mul(h1_opening(&pad, t, b)))
                })
            })
            .collect();
        let expected = interpolate(&expected_samples);

        let zero_pad = [QM31::ZERO; ROWS];
        let actual_samples: Vec<_> = (0..SAMPLES)
            .map(|sample| {
                let t = lift(sample as u32);
                (0..512).fold(QM31::ZERO, |sum, b| {
                    let p = point(t, b);
                    let before = evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(
                        &prepared.public, &compiled.public_statement, &claims(&compiled.semantic_c1.c1, &zero_pad, &p),
                        &p, lambda, chi, theta, &zero_point, mu, eta,
                    ).expect("valid selected terminal");
                    let after = evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(
                        &prepared.public, &compiled.public_statement, &claims(&compiled.semantic_c1.c1, &pad, &p),
                        &p, lambda, chi, theta, &zero_point, mu, eta,
                    ).expect("valid selected terminal");
                    sum.add(after.sub(before))
                })
            })
            .collect();
        let actual = interpolate(&actual_samples);
        assert_eq!(actual, expected, "complete terminal response disagrees with Copy matrix");
        assert_eq!(actual[0], actual_samples[0], "initial boundary c0 is not recovered");
        for (sample, value) in actual_samples.iter().enumerate() {
            assert_eq!(evaluate(&actual, lift(sample as u32)), *value, "compact coefficient order");
        }
        assert!(actual[12..].iter().all(|coefficient| *coefficient == QM31::ZERO),
            "H1 response reaches c12..c27");
        let c1 = actual[1];
        assert_eq!(c1, actual_samples[1].sub(actual[0]).sub(
            actual.iter().skip(2).fold(QM31::ZERO, |sum, coefficient| sum.add(*coefficient))
        ), "c1 reconstruction from the real polynomial");
    }
}
