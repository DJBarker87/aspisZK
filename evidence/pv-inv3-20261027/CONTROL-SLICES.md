# Control-only checks

These harnesses are bounded structural source slices, not an extraction or installed equivalence. No field inversion or multiplication occurs; no inverse stubs or arithmetic assumptions occur. Harness assumptions restrict valid row/bit inputs only.

- tail_mask_index: pair_forest_hiding.rs:190–196 and host_semantic.rs:289, tail rows 768–1023.
- mask_dedup / mask_sort_swap: pair_forest_hiding.rs:185–186,193–196; OR is idempotent and permits adjacent swaps. Full list transport is Lean MaskRowFold, not inferred from two rows.
- static_slot_guard: host_semantic.rs:329–334, reject before indexing and arity increment.
- zero_weight_overwrite: pair_forest_trace.rs:655–665, zero weight preserves first free slot; verifies why static and dynamic slots differ.
- guard_no_early_exit: host_semantic.rs:293–295; four bool comparisons, including those after a false result. This does not prove machine timing or limb-comparison trace equality.

Expected work: Kani translation and the named finite control assertion. No chained field arithmetic or long Rust numerical gate.
