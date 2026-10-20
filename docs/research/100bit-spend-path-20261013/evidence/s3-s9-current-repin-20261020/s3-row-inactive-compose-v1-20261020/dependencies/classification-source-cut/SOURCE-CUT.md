# S3 inactive classifier source cut

This small extraction target is the actual `aspis_core::r0::opening::inactive` helper used by the source classification oracle. Its `Error` enum, `COPY_ACTIVE_ROW_MASKS` constant, and function body are copied byte-for-byte from the pinned current source at the line spans recorded in `input/source-pins.json`. `check-source-cut.py` verifies all three copies and their full-file hashes. The minimized crate retains the same `crate::r0::opening` path and adds only the import of the parent `Error` type required by nesting. It excludes unrelated `opening.rs` functions.

The extraction target does not include `weights.rs` grouped-loop execution. The existing Lean S3 table theorem already proves the 64x16 table cells match the source row/mask formula. This extraction is intended only to check the small executable range/error/bit-selection helper, not to duplicate that finite table proof or claim full `Weights::pair` refinement.
