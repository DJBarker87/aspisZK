# R333 source traversal frontier archive (draft)

This untracked staging directory contains byte-for-byte recursive copies of the saved R322, R323, R327, R330, and R331 evidence trees. `frontier-manifest.json` is a metadata-only index of paths, SHA-256 values, selected receipts, and observed extraction/translation outcomes. `FILES.sha256` checks every file in this archive, including the manifest and this note; copied nested `SHA256SUMS` files remain untouched and are inventoried as files.

R327 extraction completed successfully (`has_errors=false`) under the saved 5 GiB/7 GiB/zero-swap/128-task cap. The root source hash and decoded root AST hash (ignoring statement IDs) are unchanged from R297. Five selected, identity-matched body rows changed from opaque to structured. The audit reports 21 reachable opaque helper functions remain.

R330 is the current first translation failure: `Nested-loop returns require exactly one Option language item` at `iterator.rs:2486:4–2490:35`, `PrePasses.ml:969`; exit 2, 0.16 seconds, peak RSS 64,768 KiB, no swap, and no generated output. R327 contains three concrete Option lang-item rows—`Option<&B>`, `Option<usize>`, and `Option<Iter<B>>`—with no `Option<ControlFlow<(), ()>>` row. This archive records that observed guard failure without selecting a remedy. R303's earlier erased-region error is historical only.

The earlier numeric-ID-only status pairing was overwritten during correction and is not preserved as a separate file; the corrected R327 audit states this explicitly. Numeric declaration IDs are table-local positions and cannot be compared across the two LLBC files without identity matching. `#print axioms` is N/A because this archive contains no Lean compilation output.

This is draft evidence staging for independent lead review, not a source-semantics or release decision. No tracked file was changed.
