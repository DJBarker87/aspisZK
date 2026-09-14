# V7 current caller source-unblock — 2026-09-14

Status: **CURRENT SOURCE TRANSLATION CLOSED; G1 SOURCE REFINEMENT OPEN**

The selected observer-capable Tag-73 verifier caller now translates through
the real `WeightAccumulator::dot`, real `qm31_dot3_separate`, full-width
`prequery_dot_256`, and snapshot call graph without a generated `sorry`.
No transcript, field, query, work, digest, relation, proof, or Pool parameter
was changed.

Focused checks performed after the normalizations:

- `field::tests::three_shared_weight_dots_match_independent_dots`: 1/1;
- `sumcheck::tests::deferred_binary_64x16_matches_legacy_at_64_random_off_domain_fold_points`: 1/1;
- `sumcheck::tests::random_line_tensors_match_materialized_weights_across_later_folds`: 1/1;
- `v7_k13_prequery_snapshot_regression`: 2/2;
- `v7_prequery_observer_next`: 7/7.

The narrow translation of the selected terminal dot and borrow-separated
three-dot path was also complete and contained no forbidden proof holes. The
complete selected-caller LLBC hash is
`cd922292f03e24a82b58090ccc5b1e49582fd9a48d1b60ecfe75a62d0f40b7a3`.

The exact next proof obligation is to kernel-import the generated reachable
graph with checked standard-library external implementations, then prove that
the literal callback invocation receives the post-round-zero six-component
accumulator consumed by
`generated_live_six_component_accumulator_corresponds`. Only after that result
is instantiated in `generated_snapshot_prechallenge_corresponds` is the
maintained pre-query discrepancy source link closed.

Runtime status remains separate: the helper refactoring is `inline(always)`
and tests preserve arithmetic behavior, but a selected SBF/artifact/CU
comparison has not yet been run for this source revision.
