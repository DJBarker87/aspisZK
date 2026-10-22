//! P6 differential for the exact selected `0usize..4usize` `Iterator::fold`
//! order and closure-state behavior. This compares the installed Rust std
//! implementation with the explicit operational loop used in the Lean model.

#[test]
fn range_fold_04_matches_explicit_ordered_loop() {
    for seed in [0u64, 1, 7, 0x1234_5678_9abc_def0] {
        let mut observed = Vec::new();
        let actual = (0usize..4usize).fold(seed, |acc, i| {
            observed.push(i);
            acc.wrapping_mul(17).wrapping_add(i as u64 + 1)
        });

        let mut state = seed;
        let mut expected_indices = Vec::new();
        for i in 0usize..4usize {
            expected_indices.push(i);
            state = state.wrapping_mul(17).wrapping_add(i as u64 + 1);
        }
        assert_eq!(observed, expected_indices);
        assert_eq!(actual, state);
    }
}
