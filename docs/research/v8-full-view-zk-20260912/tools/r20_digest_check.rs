// Test snippet injected inside the existing semantic-terminal `tests` module.
// It compares the staged candidate against both retained implementations.

fn r20_random_digest(state: &mut u64) -> Digest {
    core::array::from_fn(|_| next_test_m31(state))
}

#[test]
fn r20_digest_candidate_matches_literal_and_tensor() {
    let (transfer_public, transfer) = transfer_at(13);
    let (withdrawal_request, withdrawal) = withdrawal_at(13);
    let mut state = 0x7262_2044_6174_6368u64;
    let mut indices = alloc::vec![0u64, 1, (1 << 19) - 1, (1 << 20) - 1];
    for _ in 0..32 {
        indices.push((next_test_m31(&mut state).0 as u64) & ((1 << 20) - 1));
    }

    // This exercises the digest helper algebra only; it deliberately does not
    // call validate_transition or claim a valid full transition witness.
    let mut check = |base: SemanticPublic<'_>, index: u64, label: &str| {
        for sample in 0..20 {
            let mut transition = match base.variant {
                CompiledVariant::PrivateTransfer => transfer.public_statement,
                CompiledVariant::Withdrawal => withdrawal.public_statement,
            };
            transition.live_snapshot.next_pair_index = index;
            transition.live_snapshot.frontier =
                core::array::from_fn(|_| r20_random_digest(&mut state));
            transition.candidate_afterstate.next_frontier =
                core::array::from_fn(|_| r20_random_digest(&mut state));
            transition.candidate_afterstate.next_root = r20_random_digest(&mut state);
            let public = SemanticPublic {
                anchor: r20_random_digest(&mut state),
                nullifier: r20_random_digest(&mut state),
                recipient: (sample & 1 == 0).then(|| r20_random_digest(&mut state)),
                change: r20_random_digest(&mut state),
                transition: &transition,
                ..base
            };
            let selectors = Selectors {
                high: core::array::from_fn(|_| next_test_qm31(&mut state)),
                low: core::array::from_fn(|_| next_test_qm31(&mut state)),
            };
            let openings = StateOnlyPoseidonOpenings {
                z: core::array::from_fn(|_| next_test_qm31(&mut state)),
                succ_z: core::array::from_fn(|_| next_test_qm31(&mut state)),
                xor12_z: core::array::from_fn(|_| next_test_qm31(&mut state)),
            };
            let literal = literal_public_digest_packed(public, &openings, &selectors);
            let tensor = public_digest_packed_selector_tensor(public, &openings, &selectors);
            let candidate = super::r20_digest_factored::public_digest_packed_selector_tensor_r20(
                public, &openings, &selectors,
            );
            assert_eq!(
                candidate, tensor,
                "{label} tensor mismatch index={index} sample={sample}"
            );
            assert_eq!(
                candidate, literal,
                "{label} literal mismatch index={index} sample={sample}"
            );
        }
    };

    for &index in &indices {
        check(
            private_public(&transfer_public, &transfer.public_statement),
            index,
            "transfer",
        );
        check(
            withdrawal_public(&withdrawal_request, &withdrawal.public_statement),
            index,
            "withdrawal",
        );
    }
}
