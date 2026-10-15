# Unified semantic density lemma evidence

The focused Lean target `R1UnifiedSemanticDensity` compiled successfully in the pinned NUC workspace on attempt `semantic-density-c`. Its source is byte-identical to the task worktree source at `docs/research/100bit-spend-path-20261013/lean/UnifiedSemanticDensity.lean` (SHA-256 `db2457d02da3ce58cec52092eab5cfbccdb4f820ed285a451c9dceb6223a0667`). The compile receipt reports exit 0, 2.43 seconds, peak RSS 3,584,992 KiB, swap 0, with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`.

The theorem `AspisR1.UnifiedSemanticDensity.semantic_density_bound` reuses `semantic_round_densityZ` with `maskClaimsR0`. Its hypotheses include the explicit prefix decoder function, the selector equality `p.σ i s = semChal s` for indices below 25, and matching prefix/decoded round lengths. It bounds the sampler's semantic bad-event mean by `rowBudget i`. This result does not prove decoder success, an acceptance implication, or correspondence to the concrete Rust source decoder.

Attempts `a` and `b` are retained as failed proof-plumbing attempts; their logs include `sorryAx`. Only attempt `c` is successful. Its `#print axioms` output is `[propext, Classical.choice, Quot.sound]`. The object archive contains only the final target object; `imports.json` records hashes of the four imported object files as resolved in the pinned workspace.
