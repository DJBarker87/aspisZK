# Actual boxed-selector marginals and bounded source high summation

The checked endpoint `SumHighBoxedModel.boxed_path_sum` derives success, canonicality and exact model value for the actual generated `sum_high` call on range57..63, using the same successful actual boxed point. Neither the selector marginals nor loop success are assumed. The inner loop theorem handles arbitrary bounded intervals and an arbitrary canonical incoming accumulator; the wrapper theorem follows the actual single-range slice iterator and cloned range.

`SelectorMarginalModel` reuses the existing `R0P.SemDegree.g2High_selAt`, `g2Low_selAt` and `selAt_eq_bitWeight` proofs from the older v8 semantic work. Its partition result holds at arbitrary field points. `SumHighModelCorrespondence` reuses `R0P.g2_fold_add` to connect the symbolic accumulator to the retained sum model. Large selector expressions and concrete field recurrences are not normalized.

`SumHighGeneratedSlice` retains the three whole generated declarations byte-for-byte in an isolated namespace; the manifest records source spans and hashes. The supplied `SumHighStdModels` implements the missing derived Range.clone by cloning its two fields with the supplied clone implementation. It adds no axiom or success stub. The pinned Rust Range declaration and existing Aeneas clone definitions are retained in range-clone-model-pins. Correspondence of this explicit library model and Rust derive/compiler behavior remains a stated trusted boundary, not a proved compiler theorem.

The enclosing path-selector multiply, complete path-family caller, schedule two-range wrapper, release-source equivalence and full accepted-spend theorem remain separate work. This checkpoint proves the shared source components and does not claim 100-bit implementation soundness.

All focused checks exited0 on the capped NUC with zero process swaps. Every theorem axiom report uses only propext, Classical.choice and Quot.sound. The generated declaration slice contains no new theorem, hence its zero reports. Exact commands, source revisions, direct-import pins, source/object hashes and resource measurements are in each receipt. No unchanged broad replay was run.

| Target | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| `SumHighStdModels` | 1.182 | 2596132 | 1 |
| `SumHighGeneratedSlice` | 1.251 | 2602820 | 0 |
| `SumHighInnerLoop` | 1.532 | 3006612 | 2 |
| `SumHighSingleRange` | 1.398 | 2996652 | 1 |
| `SumHighModelCorrespondence` | 1.868 | 3809696 | 2 |
| `SelectorMarginalModel` | 1.832 | 4040656 | 5 |
| `SumHighBoxedModel` | 2.077 | 4041340 | 2 |
