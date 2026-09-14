//! R14 actual compiler/terminal offset extraction. DRAFT, not compiled in Chat.
//!
//! Install as a child of tests/r10_semantic_cut.rs (see INTEGRATION.md).
//! This reuses its genuine deterministic compiler fixture. The entry digest
//! stands for an already processed public C2 prefix; no C2 simulation or
//! actual generated q22 execution is claimed by this test.
use super::*;
use aspis_core::{
    state_only_hiding::{begin_state_only_masked_sumcheck, state_only_explicit_g_mask_factor},
    transcript::{label, Transcript},
};
use aspis_prover::state_only_hiding::state_only_initial_mask_claim;
use aspis_statement::pool_v1::build_pool_v1_pair_forest_copy_helper_v1;
use sha2::{Digest as ShaDigest, Sha256};

fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha256::new();
    for part in parts {
        h.update(part);
    }
    h.finalize().into()
}

fn at(prefix: &[QM31], t: QM31, suffix: usize) -> [QM31; 10] {
    let j = prefix.len();
    assert!(j < 10);
    let mut p = [QM31::ZERO; 10];
    p[..j].copy_from_slice(prefix);
    p[j] = t;
    for k in j + 1..10 {
        p[k] = lift(((suffix >> (9 - k)) & 1) as u32);
    }
    p
}

fn with_g(
    c1: &[Vec<M31>; 16],
    h1: &[QM31; ROWS],
    g: &[QM31; ROWS],
    p: &[QM31; 10],
) -> [QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1] {
    let mut out = claims(c1, h1, p);
    for (i, z) in [*p, successor_point(p), xor12_point(p)].iter().enumerate() {
        out[i * 28 + 27] = multilinear_evaluate_qm31(g, z).unwrap();
    }
    out
}

#[test]
fn r14_source_offsets_are_g_independent_at_actual_eta_and_round_challenges() {
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
    .expect("1024 helper rows");
    let inactive = inactive_rows();
    let mut g = core::array::from_fn::<_, ROWS, _>(|i| QM31 {
        c0: CM31::new(M31((i + 1) as u32), M31((2 * i + 3) as u32)),
        c1: CM31::new(M31((3 * i + 5) as u32), M31((5 * i + 7) as u32)),
    });
    let pivot = inactive[0];
    g[pivot] = inactive
        .iter()
        .filter(|&&i| i != pivot)
        .fold(QM31::ZERO, |s, &i| s.add(g[i]))
        .neg();
    let zero = [QM31::ZERO; ROWS];
    let masks: [Vec<M31>; 10] = core::array::from_fn(|_| vec![M31::ZERO; ROWS]);
    let initial = state_only_initial_mask_claim(&compiled.semantic_c1, &masks, &g).unwrap();
    let initial_zero = state_only_initial_mask_claim(&compiled.semantic_c1, &masks, &zero).unwrap();
    let mut fs = Transcript::new(hash);
    // A named public diagnostic prefix, NOT a production deployment binding.
    fs.absorb(label::STATEMENT, b"R14-actual-terminal-offset-fixture");
    let eta = begin_state_only_masked_sumcheck(&mut fs, initial).unwrap();
    let mut prefix = Vec::new();
    let mut boundary_claim = initial;
    for round in 0..3 {
        let mut real = [QM31::ZERO; 28];
        let mut baseline = [QM31::ZERO; 28];
        let mut only_g = [QM31::ZERO; 28];
        for sample in 0..28 {
            let t = lift(sample as u32);
            for suffix in 0..(1usize << (9 - round)) {
                let p = at(&prefix, t, suffix);
                let eval = |table: &[QM31; ROWS]| {
                    evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(
                        &prepared.public, &compiled.public_statement,
                        &with_g(&compiled.semantic_c1.c1, &helper, table, &p),
                        &p, lambda, chi, theta, &zero_point, mu, eta,
                    ).unwrap()
                };
                real[sample] = real[sample].add(eval(&g));
                baseline[sample] = baseline[sample].add(eval(&zero));
                only_g[sample] = only_g[sample].add(
                    state_only_explicit_g_mask_factor(&p)
                        .mul(multilinear_evaluate_qm31(&g, &p).unwrap()),
                );
            }
            assert_eq!(real[sample], baseline[sample].add(only_g[sample]));
        }
        let polynomial = interpolate(&real);
        let beta = interpolate(&baseline);
        let gp = interpolate(&only_g);
        for k in 0..28 {
            assert_eq!(polynomial[k], beta[k].add(gp[k]));
        }
        assert_eq!(real[0].add(real[1]), boundary_claim);
        if round == 0 {
            assert_eq!(initial_zero.add(only_g[0]).add(only_g[1]), initial);
        }
        let mut frame = Vec::with_capacity(433);
        frame.push(round as u8);
        for k in core::iter::once(0).chain(2..28) {
            let mut bytes = [0u8; 16];
            polynomial[k].write_le_bytes(&mut bytes);
            frame.extend_from_slice(&bytes);
        }
        fs.absorb(label::V6_COMPACT_SEMANTIC_ROUND, &frame);
        let challenge = fs.challenge_qm31().unwrap();
        boundary_claim = evaluate(&polynomial, challenge);
        prefix.push(challenge);
    }
    assert_eq!(prefix.len(), 3);
}
