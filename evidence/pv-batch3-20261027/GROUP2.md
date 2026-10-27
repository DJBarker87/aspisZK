# Group 2 candidate: op222 / op224

New host_multilinear module is behind `#[cfg(feature="prover")]` in cost-probe lib.rs. It copies sparse_eq_weights into a 1,024-slot Copy carrier with logical length, retains the literal Boolean suffix test, field operation order and column.len()!=1024 -> None branch. Host semantic and simulator calls are redirected; original shared statement evaluator is unchanged.

The forest module remains behind aspis-prover/prover. Its copied row builder now returns an owned 1,024-row carrier. Tuple-value/compression loops are explicit index loops, and the original first-zero-weight slot behavior is retained. The copied op224 helper returns an owned 1,024-field carrier, processes producers before consumers in slot order, skips zero weights and maps the first inversion failure to CopyImbalance. A materializing adapter preserves the existing host Vec interface. No arithmetic is regrouped.

The forest projection is +31.6399 microseconds on each fixture. Group 2 gates pending. Op224's microbenchmark includes the registry dependency, so its projection must replace (not double-count) the forest registry contribution of the helper call.

Early unchanged-extractor preflight on forest134-01 failed `escaping reference output requires loan validation` before emission; retained as extraction refusal, not a checked row counterexample or a Lean compile. The full include closure must be inspected and narrowed to the actual root before deciding which source helper needs an owned replacement. The guard is not changed.

Focused corrections: check01 rejected the newly introduced use-before-inner-doc ordering and a missing new module in the host source manifest. Imports now follow the inner documentation, and source staging enumerates tracked crate files. Check02 passed. The forest134 LLBC identifies exactly one reference-output declaration: core::array's range index returning a slice, introduced by endpoint_counts(&links.data[..links.len]). The source now passes the fixed array and logical length separately; this removes that loan without weakening the guard or changing endpoint order. No failed extraction is rerun unchanged.
