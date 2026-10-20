# Actual loop-1 mask/body step (focused evidence)

This target proves the actual generated loop body's successful `some` branch and the U16 shift/AND predicate used by the 16-entry inner loop. `actual_mask_test_matches_bit` establishes that the generated nonzero test selects exactly the corresponding bit of the actual mask. `body_some_step` then gives the field-value update when the generated add succeeds. The next full-loop proof must still establish the iterator lifecycle, operation success, and the 16-step fold invariant; this packet makes no loop-totality claim.

The accepted target is `S3ActualLoop1BodyStepV1` using Lean 4.32.0, `-M 4400`, `-j1`, default heartbeat/recursion settings, and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Receipt, preflight, command, timing, admission, and reservation files are in `attempt-v11/`. The imported actual loop-0 composition owner source and its producer evidence are mirrored here. Object binaries are not included.

The preceding v1-v10 attempts are diagnostic-only and not accepted; the proof evolved through source typing/branch and scalar shift/AND lemma corrections.
