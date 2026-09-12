// Paste this test directly inside the existing `tests` module in
// `crates/aspis-prover/src/pool_v1_pair_forest_honest.rs` in an isolated
// source copy. It deliberately reuses that module's private `transfer_fixture`,
// `run_transfer`, and imported payment helpers. This exact body passed against
// target commit 9e432896a4e1515efebe940b71fd9b4f9f009189.
//
// It exercises the actual honest compiler, mask builder/application, and full
// circle encoder. The generated experiment's three-line positive overwrite is
// repeated literally because that module is not compiled into aspis-prover.
#[test]
fn diagnostic_q22_certificate_on_valid_positive_transfers() {
    use crate::circle_candidate::CircleEncoder;
    use crate::state_only_entropy::StateOnlyAttemptSecrets;
    use crate::state_only_hiding::{
        apply_pool_v1_pair_forest_mask_material_v1, InMemoryStateOnlyMaskNonceStore,
    };
    use aspis_core::field::P;
    use aspis_core::state_only_hiding::StateOnlyHidingContext;

    const LAMBDA: [u32; 88] = [
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        1508290849, 1480589898, 639192798, 666893749, 0, 0, 0, 0,
        2147483646, 0, 1, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0,
    ];
    const DESCRIPTOR: [u8; 107] = [
        65,86,56,47,112,111,115,105,116,105,118,105,45,116,114,97,110,115,102,101,
        114,47,97,99,116,105,118,101,45,99,101,108,108,45,111,118,101,114,119,114,
        105,116,101,47,108,97,110,101,57,52,47,118,49,121,147,51,56,96,194,205,16,
        170,24,62,117,31,39,16,186,39,155,51,42,187,191,221,206,119,59,50,23,103,
        240,1,186,246,3,3,94,209,133,66,79,213,243,218,249,137,113,108,165,69,18,
        102,107,218,14,
    ];

    fn functional(encoder: &CircleEncoder, message: &[M31]) -> M31 {
        let encoded = encoder.encode_c1_message(message).unwrap();
        LAMBDA.iter().enumerate().fold(M31::ZERO, |acc, (i, &coefficient)| {
            assert!(coefficient < P);
            acc.add(M31(coefficient).mul(encoded[i]))
        })
    }

    let encoder = CircleEncoder::new_for_domain_log(20);
    let row_weight = {
        let mut unit = vec![M31::ZERO; 1024];
        unit[1014] = M31::ONE;
        functional(&encoder, &unit)
    };
    assert_eq!(row_weight, M31(170822063));

    for recipient_value in [1u32, 100, 400, 500, 600, 900, 999] {
        let change_value = 1_000 - recipient_value;
        let mut fixture = transfer_fixture();
        fixture.witness.recipient.value = recipient_value;
        fixture.witness.change.value = change_value;
        fixture.public.recipient_commitment = pool_v1_note_commitment(
            &fixture.witness.recipient.owner_key,
            recipient_value,
            fixture.public.asset_id,
            &fixture.witness.recipient.salt,
        );
        fixture.public.change_commitment = pool_v1_note_commitment(
            &fixture.witness.change.owner_key,
            change_value,
            fixture.public.asset_id,
            &fixture.witness.change.salt,
        );
        let checked = run_transfer(&fixture).unwrap();
        let semantic = checked.compilation.semantic_c1;
        assert_eq!(semantic.c1[1][1014], M31(recipient_value));
        assert_eq!(semantic.c1[1][1015], M31(change_value));
        assert_eq!(semantic.c1[3][1014], M31::ZERO);
        let semantic_l = functional(&encoder, &semantic.c1[3]);
        let inverse = M31(recipient_value).mul(M31(change_value)).inv();
        let expected_final = semantic_l.add(row_weight.mul(inverse));

        for seed in [1u8, 7, 19] {
            let binding = [42u8; 32];
            let mask_binding = crate::host_hashv(&[
                b"AV8/positive-transfer/legacy-mask-stream/v1",
                &DESCRIPTOR,
                &binding,
            ]);
            let context = StateOnlyHidingContext::pool_v1_pair_forest_v1(binding, [seed; 32]);
            let attempt = StateOnlyAttemptSecrets::deterministic_spend_fixture(
                [seed; 32], [seed + 1; 32], [seed + 2; 32],
            );
            let (_, material) = attempt
                .reserve_and_build_pool_v1_pair_forest_mask_material_v1(
                    crate::HOST_HASH,
                    mask_binding,
                    context,
                    &mut InMemoryStateOnlyMaskNonceStore::default(),
                )
                .unwrap();
            let mut trace = semantic.clone();
            apply_pool_v1_pair_forest_mask_material_v1(&mut trace, material).unwrap();
            assert_eq!(trace.c1[1][1014], M31(recipient_value));
            assert_eq!(trace.c1[1][1015], M31(change_value));
            let before_overwrite_l = functional(&encoder, &trace.c1[3]);
            trace.c1[3][1014] = trace.c1[1][1014].mul(trace.c1[1][1015]).inv();
            let final_l = functional(&encoder, &trace.c1[3]);
            assert_eq!(final_l, expected_final);
            println!(
                "Q22_TRACE recipient={} change={} seed={} semantic_l={} inverse={} before_overwrite_l={} final_l={} recipient_commitment_1={} change_commitment_1={}",
                recipient_value, change_value, seed, semantic_l.0, inverse.0,
                before_overwrite_l.0, final_l.0,
                fixture.public.recipient_commitment[1].0,
                fixture.public.change_commitment[1].0,
            );
        }
    }
}
