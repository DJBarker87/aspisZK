# Remaining independent native gates

These are first attempts on distinct obligations, not retries of the timed-out masks graph. Every command uses the pinned KANI-CONFIG mitigation: optimized profile, CPU0–3, jobs4,6G/8G/swap0,TasksMax64, no stubs, explicit unwind assertions, and a180s initial deadline. Compilation and CBMC symbolic checking are the expected phases. The runner snapshots every Rust source/manifest before admission. Receipt success, not this plan, determines results.

| harness | domain | unwind | role |
|---|---|---:|---|
|pool_v1::hiding::pv_cbm_checks::classifier_all_usize|arbitrary usize row/column; no assumptions|25|strengthens private classifier prerequisite|
|schedule_checks::schedule_success|no inputs; complete schedule Result|137|schedule success/length prerequisite|
|checks::rows_complete|no inputs; complete shipped/reference Result|257|op133 P6 native association gate|
|cell_checks::cells_complete|no inputs; complete shipped/reference Result|1025|op132 P6 native association gate|
|index_checks::encoder_pair_order|arbitrary1024 u16 values; chunks_exact/zip vs indexed pair reads|513|op79 iterator/index trace prerequisite; no field equivalence|
|index_checks::suffix_scan_order|arbitrary10 coordinate classes0/1/non-Boolean|12|op222 suffix iterator vs indexed scan prerequisite|
|index_checks::sparse_row_bounds|arbitrary valid prefix length, prefix and suffix|2|op222 bounds and bit decomposition prerequisite|

Direct source extraction still fails closed at the pinned backend guards. Owned mutable-output reference extraction is acceptable prerequisite evidence, but its fresh-vector/Result association must also be justified before crediting a complete source law. No third masks retry is permitted or planned.

Lead ruling(k), read before any arithmetic gate was launched: the planned QM31 evaluator and partial multilinear arithmetic gates were removed from the cfg(kani) harness module, not run. Their remaining field proof obligations must use extraction plus a Lean/structural source link. Owner decision(j) leaves the capped trust list unchanged. Replacement control-flow models are explicitly prerequisites, not shipped-function ROW comparisons.
