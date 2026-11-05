fn NHU_poseidon_selectors_cut(selectors: &Selectors,log:&mut SumLog) -> StateOnlyPoseidonSelectors {
    StateOnlyPoseidonSelectors {
        block: sum_cut(selectors, &[0..57],log),
        local: selectors.low,
    }
}
