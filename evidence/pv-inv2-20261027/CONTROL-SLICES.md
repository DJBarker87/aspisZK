# Control slice scope

Six bounded control checks (not P6 shipped arithmetic equivalence):

- path_base_bounds: pair_forest_hiding.rs:63–78, with the fixed 6×4 base array collapsed to its identical row [1,5,9,13].
- path_target_bounds: :81–90, preserving None and the level≤20 branch.
- aux_translation_bank: pair_forest_trace.rs:522–533, row translation; row<976 is the old schedule domain, not a global native-input assumption. Selection (544..864) from tuple_cells :492.
- tuple_cell_index: :499–507, bounded start/count/lane; covers index and final-lane tweak control only.
- two_slot_position: :657–660, copied zero-weight first-position predicate; arbitrary u32 weights, no field multiplication.
- masks_index: pair_forest_hiding.rs:191–199, shifts and mask-index bounds for bounded native rows.

No field inverse or chained multiplication is stubbed or run. These checks do not establish native registry enumeration, tuple-bank join, canonicality, caller validity or observer equality. The Lean reference/P obligations retain those gaps.
