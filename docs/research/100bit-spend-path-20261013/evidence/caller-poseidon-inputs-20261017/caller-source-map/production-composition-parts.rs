fn composition_parts(
    public: SemanticPublic<'_>,
    claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
    point: &[QM31; 10],
    lambda: QM31,
    chi: QM31,
    theta: QM31,
) -> Result<
    (
        QM31,
        [QM31; 16],
        [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
        QM31,
        QM31,
        QM31,
    ),
    PoolV1PairForestSemanticTerminalErrorV1,
> {
    let invalid_amount = match public.withdrawal_amount {
        None => false,
        Some(amount) => amount == 0 || amount >= (1 << 30u32),
    };
    if invalid_amount {
        return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidPublicAmount);
    }
    validate_transition(public)?;
    let openings = StateOnlyPoseidonOpenings {
        z: core::array::from_fn(|column| selected_claim(claims, 0, column)),
        succ_z: core::array::from_fn(|column| selected_claim(claims, 1, column)),
        xor12_z: core::array::from_fn(|column| selected_claim(claims, 2, column)),
    };
    let mask_only = core::array::from_fn(|column| {
        selected_claim(
            claims,
            0,
            POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + column,
        )
    });
    let selectors = Selectors::boxed_at_point(point);
    let poseidon =
        evaluate_state_only_poseidon_oracle_projected(&openings, &poseidon_selectors(&selectors));
    let semantic = semantic_packed(public, &openings, &selectors);
    let h1_z = selected_claim(claims, 0, SELECTED_H1_COLUMN);
    let copy = evaluate_with_selectors(
        &openings.z,
        h1_z,
        &selectors,
        lambda,
        chi,
        public.transition.live_snapshot.next_pair_index,
        copy_variant(public.variant),
    );
    let prepared_theta = PreparedQm31Multiplier::new(theta);
    let mut composition = copy.residual;
    for lane in semantic.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    for lane in poseidon.into_iter().rev() {
        composition = prepared_theta.mul(composition).add(lane);
    }
    Ok((
        composition,
        openings.z,
        mask_only,
        selected_claim(claims, 0, SELECTED_G_COLUMN),
        h1_z,
        copy.active,
    ))
}
