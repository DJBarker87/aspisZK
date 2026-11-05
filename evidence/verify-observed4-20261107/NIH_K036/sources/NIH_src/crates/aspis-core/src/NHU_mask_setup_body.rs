fn NHU_mask_setup_cut(coefficients:&[QM31;27],linear:QM31)->(PreparedQm31Multiplier,QM31){
    let prepared_linear = PreparedQm31Multiplier::new(linear);
    let mut shared = coefficients[STATE_ONLY_HIDING_FACTOR_DEGREE];

(prepared_linear,shared)
}
