# Selected inactive-mask reuse check

This small read-only check compares the 64 `COPY_ACTIVE_ROW_MASKS` values and inactive-row predicate in current `crates/aspis-core/src/r0/opening.rs` with the old Lean `R0P.copyActiveRowMasks` and `AspisR19.T163SourceTable.inactiveBlocks` / `isInactive` definitions. It parses source literals, compares all 64 mask entries and all 1,024 row booleans, verifies pinned source hashes, and exits nonzero on any difference.

The comparison passed: the mask arrays are identical, the two inactive-row computations agree on every row, and the inactive count is 810. Reusable Lean names include `R0P.CopyActiveRow`, `R0P.copyInactiveRows`, and `AspisR19.T163SourceTable.inactive`. This is a numeric/source-text comparison only; it is not a Rust-to-Lean refinement proof and does not close J2.

Run from any directory with `python3 <bundle>/check.py`; `comparison.json` records the checked values and SHA-256 source pins.
