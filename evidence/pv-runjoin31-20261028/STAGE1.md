# Native lane-root correspondence — checked

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

Checked so far: `LaneFold31.step_original` / `fold_append` (44600),
`LaneRecipe31.recipe_success` (44602), `LaneCounts31.count` / `shift` (44617),
`LaneDenotation31.complete_result` (44626), the original branch transport
(44634), and both complete witness/error roundtrips (44635), all standard axioms and zero
swap. The uniquely named enum/child/body cohort is checked at 44610, 44618 and
44621. Denotation now normalizes only explicit Result binds and twenty array
reads; it never unfolds a hash.

Checked: installed native dictionary (44652), symbolic parent fold (44653),
successful leaf transport (44654), complete root field meaning (44655), and
the canonical-route transfer/withdrawal specialization (44658). The last target
passed in 5.174 seconds, peak RSS 5,010,776,064 bytes, zero swap, standard axioms.
Signed-shift, import/discriminant, bound/name and Result sequencing failures
are retained. The signed-shift failure was replaced by regenerated Rust and
emission, never by an executable Lean body edit.

No semantic Admission, unconditional HonestInput, owner coverage or V038/V045
closure is claimed. Endpoint premises removed/added/weakened remain 0/0/0.
Reservation refusals are retired IDs and wait the full 180 seconds; tally.json
and the individual receipts are the authoritative running resource record.

## Final preflight qualification

Expanded final LaneDenotation31 closure validation exposed imported source/cache
discrepancies; see FINAL-AUDIT-SCOPE.md and recovery/lane-audit-cache-mismatches.json.
The focused receipts, structural binding and finite differential remain evidence,
but coherent native source-law closure is unconfirmed. No mismatched object was
replaced or recompiled. No fresh lane closure audit is claimed.
