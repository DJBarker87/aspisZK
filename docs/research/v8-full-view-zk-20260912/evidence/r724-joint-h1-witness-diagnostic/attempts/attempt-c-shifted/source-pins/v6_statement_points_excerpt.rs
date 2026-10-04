
fn fold_values_prefix<const INPUT: usize>(values: &mut [QM31; V6_FINAL_QM31_VALUES], alpha: QM31) {
    debug_assert!(INPUT <= V6_FINAL_QM31_VALUES && INPUT % 4 == 0);
    let alpha2 = alpha.square();
    let alpha3 = alpha2.mul(alpha);
    let prepared = [
        PreparedQm31Multiplier::new(alpha),
        PreparedQm31Multiplier::new(alpha2),
        PreparedQm31Multiplier::new(alpha3),
    ];
    let next_len = INPUT / 4;
    for index in 0..next_len {
        let offset = 4 * index;
        values[index] = qm31_add_sum_products3_prepared(
            values[offset],
            &prepared,
            &[values[offset + 1], values[offset + 2], values[offset + 3]],
        );
    }
}

