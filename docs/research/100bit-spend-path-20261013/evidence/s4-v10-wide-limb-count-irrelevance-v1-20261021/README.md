# V10 `wideLimbCount` slot irrelevance

For every operation record and arbitrary count result, replacing only `wideLimbCount` leaves the literal V10 helper and four-call outer results unchanged, including failures and divergence. The proofs are `literal_helper_independent_wide_limb_count` and `literal_outer_independent_wide_limb_count`; they reduce by record case split and definitional equality because these literal bodies never project the count slot.

The target is the source-shaped V10 helper/outer cut, not the fixed-v6 implementation. This establishes that `wideLimbCount` is not a residual operation dependency in the literal candidate bodies; it does not close source installation or other external slots.

Lean 4.32.0, exit 0, 32.392 seconds, 3,468,525,568 bytes maximum RSS, 0 swaps; only standard axioms. The exact selected import path and helper/outer source/object pins are included. No compiled objects are included.
