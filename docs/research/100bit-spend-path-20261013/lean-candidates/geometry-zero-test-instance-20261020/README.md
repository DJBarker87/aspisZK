# R17 query-value any/nonzero proof packet

This packet records four green Lean targets for the source-shaped `SliceIter`/`any` path and the successful actual `query_values_entry` path. It contains Lean sources and the per-attempt command, config, preflight, receipt, timing, and Lean logs. It intentionally contains no compiled objects.

## Ordered proof chain

1. `R17SliceAnySourceV1` (`sources/R17SliceAnySourceV1.lean`) proves the source-shaped `queryZeroAny_false_sound` result: successful `false` means every value yielded by the modeled `SliceIter` is nonzero. The model follows the core `Iterator::any` macro and uses the accepted iterator-next model. The exact Rust macro source is pinned in the attempt config/preflight and is summarized in `BOUNDARIES.md`.
2. `R17QueryValuesAnyInputV1` (`sources/R17QueryValuesAnyInputV1.lean`) inverts successful `queryValuesWithAny` to recover its actual five-element iterator input and `i = 0`.
3. `R17QueryValuesEntryActualInputBridgeV1` (`sources/R17QueryValuesEntryActualInputBridgeV1.lean`) strengthens the accepted v34 `queryValuesEntry` success theorem using exact owner `R17QueryValuesEntryActualDefsV1` (source SHA `14893288a301656546585eb2bf7a39997c9009caf0a51ba385c53487ef3a3de3`, object SHA `a3bdcfe1f1f60fc7a2a71433a969496d97c4b9cd3ff0ad6ba4ca9378160a1216`). It retains the exact returned array, start-zero iterator, and false callback result.
4. `R17QueryValuesActualAnyNonzeroV1` (`sources/R17QueryValuesActualAnyNonzeroV1.lean`) composes the verbatim-emitted-body adapters and the previous results: successful actual raw helper output implies every raw output word is nonzero and every decoded field output is nonzero.

Each individual `receipt.json` records exit status 0, wall time, peak process RSS, cgroup peak, and swap. The Lean reports use only `[propext, Classical.choice, Quot.sound]` for the targets audited. Preserve the configs and preflights as the authoritative toolchain/import pins; do not infer an absent source revision from these historical records.

## Scope boundary

The helper theorem is about the exact emitted query-values body connected through the accepted v34 entry owner and explicit callees. The `Iterator::any` step is source-shaped and specializes the core macro with the modeled `SliceIter.next`; it is not a complete Aeneas extraction or proof of the Rust standard library implementation. The packet does not claim the entire outer `QueryGeometry`/Vec path or the std-library callback implementation is closed.

## Geometry composition instance

`GeometryConcreteQueryValues` instantiates the checked indexed geometry input/inversion candidate with the exact emitted helper body, current checked arithmetic and the source-shaped iterator-any specialization. A transparent Error.Query type adapter preserves successful values and outer fail/divergence. The new theorem discharges `NonzeroOutputs` internally, then derives canonical ordered individual inverses and the exact grouping-callback slot theorem. No abstract nonzero-output premise remains in those concrete composition statements.

This is still a composition CANDIDATE because Rust std Iterator.any source correspondence, original input/prefix iterator equivalence/adoption, whole grouping map/from_fn/collect, complete frozen caller and runtime remain OPEN. Documentation discrepancies about a macro path/checker are corrected in metadata-correction.json; pinned proof sources were not altered or replayed. Five focused selected targets have standard-only audits, default Lean limits and zero swap; retained dependencies are referenced. No production source changes or binaries.
