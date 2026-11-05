fn NHU_mask_opening_cut(point:&[QM31;10],log:&mut LinearsLog)->(QM31,QM31,[QM31;27]){
    let (linear, explicit_linear) = linears_cut(point,log);
    let mut coefficients = [QM31::ZERO; STATE_ONLY_HIDING_FACTOR_DEGREE + 1];

(linear,explicit_linear,coefficients)
}
