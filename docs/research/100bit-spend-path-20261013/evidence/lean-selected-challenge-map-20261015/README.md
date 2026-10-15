# Selected challenge map

This focused Lean bundle records the selected 33-row mathematical challenge dispatch and its exact model equalities. Attempt `selected-challenge-map-a` compiled successfully, then `selected-challenge-map-b` compiled successfully after adding `first_circle_view` and `second_circle_view`; `a` is therefore retained as a superseded successful source, not a failure or independent validation of the final source.

The final source exports the semantic, gamma, ordinary-opening, circle-parameter, row-31-zero, and rho-row identities against the existing modulo-rank sampler models. Rows 25/26 remain wide embedded QM31 parameters at `sigma`; `rhoOf` extracts the QM31 parameter used by the row-specific circle maps. The module is a model-level challenge mapping only. It does not prove current Rust sampler refinement, a complete R1 transcript/protocol connection, or D1/D2/D3 closure.

The target was compiled with the pinned NUC snapshot runner, `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`. Final attempt b exited 0 in 1.70 s, peak RSS 3,561,144 KiB, swap 0. Its eight successful `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The one unused-simp-argument warning is retained in the output log.
