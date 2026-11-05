fn NHU_mask_tail_cut(shared:QM31,explicit_linear:QM31,explicit_g:QM31,log:&mut TailLog)->QM31{
    shared.add(
        multiply_tail(QM31::ONE.add(power_tail(explicit_linear,log)),explicit_g,log),
    )
}
