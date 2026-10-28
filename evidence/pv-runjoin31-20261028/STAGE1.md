# Native lane-root correspondence — in progress

The frozen body is `crates/aspis-statement/src/pool_v1/pair_forest_trace.rs:93`.
It validates/hashes the pair leaf, maps its error, traverses membership siblings
0–19 in order, and returns the resulting digest. It writes only local `current`.

Direct optimized and built MIR both extract error-free LLBC, but Aeneas fails
in InterpAbs.merge_abs_conts at the loop. Ownership/step-helper loop candidates
also fail. All inputs and diagnostics are retained. No failure is a counterexample.

The current owned reference takes the Copy witness by value and unrolls the
fixed loop, with an owned step helper and unsigned counts 0–19. Structural
binding is checked by `tools/pv-runjoin31-20261028/structural.py`. It checks every
remaining token, constants, operand order, leaf error map and output. The raw
emission is from `pv31-lane-reference-aeneas-07`; constructor rename metadata is
reversible and executable LLBC is unchanged. `source-audit.py` checks nominal
installation changes and all twenty returned current writes. Templates with
unfilled external declarations are evidence only, never imported.

Evidence class: **structural (K-1 substitute)**. This is not a Kani PASS.
`pv31-lane-differential-02` is optimized finite validation: 4,096 same-input
complete-Result comparisons with a name-only copy of the frozen body, including
successful paths, high index bits and leaf rejections. Native -01 was a retained
probe type error, corrected before -02. No shipped source was edited.

Checked so far: `LaneFold31.step_original`, `LaneFold31.fold_append`, and
`LaneRecipe31.recipe_success`, with standard axioms only. These are generic
symbolic facts, not an accepted native correspondence yet.

Pending focused checks: uniquely named enum cohort, explicit shift-count
transport, the reference's complete Result denotation, lossless outer ABI and
error adapters, and the installed native lane dictionary. Import/discriminant
and signed-shift emission failures are retained. The signed-shift failure was
replaced by regenerated Rust/emission, never an executable Lean body edit.

No semantic Admission, unconditional HonestInput, owner coverage or V038/V045
closure is claimed. Endpoint premises removed/added/weakened remain 0/0/0.
Reservation refusals are retired IDs and wait the full 180 seconds; tally.json
and the individual receipts are the authoritative running resource record.
