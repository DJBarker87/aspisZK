# Actual initialized Copy powers

`AspisR1.CopyPatternPowersExact.initialized_powers_exact` proves the actual extracted source power loop, started with the source zero-filled 16-element array, lambda, and cursor zero, succeeds, returns a canonical array and cursor 16, and decodes to the retained `R0P.copyPowers` of that same lambda. The sole input hypothesis is canonicality of lambda. It assumes no arithmetic, array-store or checked-increment success.

The fuel induction preserves the processed prefix and uses the existing checked field multiplication and array-update theorems. A small recurrence lemma identifies the retained iterative fold at successive cursors; no concrete power or 16-step field expression is normalized. `ArrayZeroExact` reuses retained scalar-zero and replicated-array facts.

The source partition contains exactly the sealed candidate width and power-loop declarations, with only a fresh namespace. The sealed candidate Funs source is SHA256 04fc129bbd54c8792d5c11e6c017e810cfc68d7a4a9577eca9455088ed04a42e; the partition source pins its exact compiled text in its receipt. This is source refinement of that indexed candidate, not an assertion of complete production extraction/runtime equivalence.

Five focused targets exited zero on the capped NUC. Exact commands, cache/source revision, source/object/direct-import hashes, wall time, peak RSS, swap and all exported axiom reports are retained. All seven behavior reports contain only propext/Classical.choice/Quot.sound; the raw source partition contains no theorem reports. No package-wide replay, dependency build, concrete recurrence expansion, or limit increase was used.

Pattern compression and registry correspondence, active selectors, full Copy evaluator/caller composition, deployed-artifact cost and the complete accepted-spend security/privacy theorem remain open.
