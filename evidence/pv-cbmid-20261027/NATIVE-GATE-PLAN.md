# Remaining independent native gates

These are first attempts on distinct obligations, not retries of the timed-out masks graph. Every command uses the pinned KANI-CONFIG mitigation: optimized profile, CPU0–3, jobs4,6G/8G/swap0,TasksMax64, no stubs, explicit unwind assertions, and a180s initial deadline. Compilation and CBMC symbolic checking are the expected phases. The runner snapshots every Rust source/manifest before admission. Receipt success, not this plan, determines results.

| harness | domain | unwind | role |
|---|---|---:|---|
|pool_v1::hiding::pv_cbm_checks::classifier_all_usize|arbitrary usize row/column; no assumptions|25|strengthens private classifier prerequisite|
|schedule_checks::schedule_success|no inputs; complete schedule Result|137|schedule success/length prerequisite|
|checks::rows_complete|no inputs; complete shipped/reference Result|257|op133 P6 native association gate|
|cell_checks::cells_complete|no inputs; complete shipped/reference Result|1025|op132 P6 native association gate|
|encoder_checks::eval_qm31_complete|all canonical QM31 coefficient limbs and both point coordinates|1025|op79 canonical-domain association candidate; actual caller invariant and WideExact still required|
|multilinear_checks::boolean_vertices|all canonical QM31 columns; Boolean vertices only|1025|op222 partial-domain prerequisite, never whole-row credit|
|multilinear_checks::one_non_boolean_prefix|all canonical QM31 columns; arbitrary canonical non-Boolean first coordinate, Boolean last9|1025|op222 partial-domain prerequisite, never whole-row credit|

Direct source extraction still fails closed at the pinned backend guards. Owned mutable-output reference extraction is acceptable prerequisite evidence, but its fresh-vector/Result association must also be justified before crediting a complete source law. No third masks retry is permitted or planned.
