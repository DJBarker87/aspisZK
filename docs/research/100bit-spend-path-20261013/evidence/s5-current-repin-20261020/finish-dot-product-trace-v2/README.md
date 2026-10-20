# S5 successful finish-query decoded-product trace v2

This focused Lean packet proves a source-derived query trace for the selected Aeneas `verifier.finish_query_dot` owner using the concrete QRaw Dot backend. It composes the actual query-loop trace, Dot product update, count-bound argument, and the accepted parser-backed `CurrentFinishField.finishField_success_canonical` theorem. The specialized `successful_current_finish_query_product_trace` no longer takes a field-canonicality callback.

The conclusion retains the final Dot state/count and an ordered list with exactly one entry per processed query index. Every entry records the actual parser-backed field read and matching `Slice.index_usize` weight read. Decoded low/high sums are the ordered sums of the actual per-query QM31 product coefficients. The `<2^46` pre-accumulator bounds follow from the source count guard `<4096`.

The final source attempt v7 exits 0, uses Lean 4.32, has zero swap, and prints only `[propext, Classical.choice, Quot.sound]` for the new theorem and its trace predecessors. Exact target, command, compiler/source hashes, wall time and peak RSS are in `evidence/trace-attempt-v7/receipt.json`.

`import-closure/selected-import-closure.json` records the QRaw, finish-count, and CurrentFinishField closure precedence and every selected object SHA. The three raw closure manifests are included; they were independently hash-verified and have zero conflicting module hashes. Compiled objects are intentionally omitted. The accepted CurrentFinishField source/receipt/lineage packet is included under `upstream/current-finish-field-owner/`.

This proves the selected generated Lean model trace. Full outer Rust caller composition, surrounding powers-array producer, runtime/library refinement beyond the accepted owners, and full S5 acceptance remain open.
