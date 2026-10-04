# R769 fixed selected point-1 entries

This bundle checks the saved M31 first coordinate for every selected R746 point-1 row entry at the fixed algebraic witness used by the R724 diagnostic. It does not establish rank, a source-to-model correspondence, H1 image coverage, a privacy simulator, or security.

The pinned saved raw matrix is `rows=222 columns=242`, SHA-256 `91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af`. The emitter reads its `point_1` row (215) and R746’s selected direction list. Lean `Fin 3` slot `s` maps to raw slot `s+1`. Seven duplicated low raw pairs are resolved to their first occurrence for R746 core columns; the later duplicates are auxiliary rows and are not selected.

R748 already proves `(47,2)` and the R769 prototype proves the densest planned direction `(127,2)`. The seven chunks prove the other 220 entries. Each proof unfolds only the four-point `sparseObservation` expression and rewrites already compiled R748/R760 finite point-weight facts before a closed M31 calculation.

Final focused runs use the pinned Lean 4.32 cached workspace with `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, no swap, and `TasksMax=128`. Chunk 00–05 each prove 32 entries; chunk 06 proves 28. All final runs exited 0, peak RSS was 3,333,116–3,336,820 KiB, swap was 0, and every printed theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The prototype’s initial missing-import attempt and Chunk 00’s pre-repair identifier attempt are retained separately. The latter exposed that R760 names `pw_0001` and `pw_0002`; correcting the formatter was the only change before the final run. No source values were recomputed or generated.

The exact sources, receipts, logs, selected-column mapping, raw input, direct import sources, and read-only cache object hashes are in [`evidence/r769-point1-selected-entries`](evidence/r769-point1-selected-entries/).

First remaining proposition: assemble the point-1 row identity, then bind point0/2, active and coefficient rows and all low-direction repairs to the full normalized source matrix. Exact target/revision/hash/exit/wall/RSS/swap and complete axioms are in every successful receipt. Fixed-witness entries do not prove universal/adaptive compatibility, native execution, oracle law, full-view simulation or soundness. Verifier CU and parameters unchanged.
