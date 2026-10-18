pub fn evaluate_state_only_poseidon_oracle_projected(
    openings: &StateOnlyPoseidonOpenings,
    selectors: &StateOnlyPoseidonSelectors,
) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
    let leading_low = selectors.local[0];
    // Preserve the source fold's initial ZERO and left-to-right operation order.
    let full_low = QM31::ZERO
        .add(selectors.local[1])
        .add(selectors.local[9])
        .add(selectors.local[10]);
    // The former inclusive range fold visits 2, 3, ..., 8 in this order.
    let internal_low = QM31::ZERO
        .add(selectors.local[2])
        .add(selectors.local[3])
        .add(selectors.local[4])
        .add(selectors.local[5])
        .add(selectors.local[6])
        .add(selectors.local[7])
        .add(selectors.local[8]);
    let leading = leading_pair_packed(openings);
    let full = interpolated_full_pair_packed(openings.z, &selectors.local);
    let internal = interpolated_internal_pair(openings.z, &selectors.local);
    let prepared_weights = [leading_low, full_low, internal_low].map(PreparedQm31Multiplier::new);
    let prepared_block = PreparedQm31Multiplier::new(selectors.block);

    crate::array_from_fn_copy::<_, 4>(QM31::ZERO, |group| {
        let start = 4 * group;
        let target = qm31_pack_base4(&openings.succ_z[start..start + 4]);
        let internal = qm31_pack_base4(&internal[start..start + 4]);
        // `active_low = leading_low + full_low + internal_low`, so the
        // four-product residual is exactly three weighted differences. This
        // removes one QM31 product per packed group without changing the
        // polynomial or its selector basis.
        prepared_block.mul(qm31_sum_products3_prepared(
            &prepared_weights,
            &[
                target.sub(leading[group]),
                target.sub(full[group]),
                target.sub(internal),
            ],
        ))
    })
}
