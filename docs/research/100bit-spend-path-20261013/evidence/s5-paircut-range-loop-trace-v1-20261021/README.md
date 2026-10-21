# S5 PairCut range-loop trace

This packet freezes the accepted-run theorem `AspisR1S5PairCutRangeLoopTraceV1.successful_run_has_trace`. It derives an ordered callback/read/scratch/push trace from a successful Aeneas `Std.loop` over `IteratorRange`, with trace length equal to `n - iter.start`.

The proof is not forward totality and keeps the reader callback explicit. The actual PairCut `weights.field` external symbol and Rust Std/LLBC refinement are still open.

`receipts/` contains the exact Lean launch and the import-only axioms audit. `dependencies/` and `evidence/producers/range-iteration/` preserve the direct imported module snapshot and its producer evidence. No OLean binaries are included.
