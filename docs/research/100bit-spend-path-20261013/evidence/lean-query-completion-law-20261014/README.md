# Query completion law focused Lean evidence

This bundle captures 16 capped attempts for six final targets, pinned to source base `617bf78f6f77c803defb65e8d5eea16babb387be`. It preserves nine failed attempts, one intermediate successful compile, and six final successful targets. Every attempt source snapshot matches its receipt source hash and sidecar. Two successful snapshots missing from the NUC evidence directory were reconstructed from current NUC source files only after exact hash comparison to the corresponding receipts; this provenance is recorded per attempt.

`R1QueryCompletionLawCheckpoint-a` failed before its dependency was fixed. Attempt `-b` compiled the identical source hash after that dependency change and passed. Both attempts remain included.

`final-sources/` contains the six final source snapshots. `objects/query-completion-law-objects.tar.gz` contains the six final Lean objects with normalized timestamps and ownership; no loose `.olean` files remain. `runner/` contains the pinned compile runner and environment snapshot. `SHA256SUMS` covers every file in this bundle except itself.
