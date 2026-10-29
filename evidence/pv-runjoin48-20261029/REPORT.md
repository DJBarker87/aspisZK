# Runjoin48 — opening source association (in progress)

Worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, entry `86e74b0a54e678d30d1c06c92c32c32cdbdb064e`.
Resume LOG D427; IDs 62600–62699 only; audits 62697–62699; 100 Lean / 0 Kani.

Target not yet established. Whole ledger rows removed: **0**.
Endpoint premises removed/added/weakened/changed: **0/0/0/0**.
`PV_RJDec_` and `PV_OWN_` are read-only. Step (4) has not started.
No wallet or account keys are involved.

## Checked progress

`ClaimThread48.complete` turns the actual claim loop into a finite ordered
traversal. `ClaimList48.complete` identifies the traversal with the coefficient
list, by induction and one named bounded read per cell. `ClaimFields48`
isolates evaluator preservation and exact flat serialization on the installed
weight dictionary. `ClaimProducerCell48.complete` proves one actual cell by
explicit field rewrites; `ClaimProducer48.complete` aggregates by list induction.
`ClaimImage48.complete` identifies the complete Result's byte image with the
ordered evaluator Results and all eight limbs' bytes. `ClaimStart48.complete`
consumes the actual entry point and capacity operation.
`ClaimInstalled48.complete` composes those source laws without assuming an
evaluation outcome. The actual evaluator callback remains explicitly visible;
this is not yet an arithmetic evaluation-to-security-model theorem.

## Validation and rejected shapes

Initial read-only preflight: 2,994 project source/object pairs, 6,275 direct
fingerprints, 5,673 external objects and 5,438 IR companions, all matching.
The inherited three rejected drafts and EndpointAudit20 remain excluded and
uncredited, as in the preceding run. A local preflight-input correction launched
no compiler. Every launch uses the existing private runjoin32-lean cache, one
module, -M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.
Admission exit 0 and allowed:true are checked in the launch shell.

62605 hit the default heartbeat limit in the mixed dictionary/cell simplifier.
It is rejected and uncredited. Its replacement, 62606/62608, isolates a named
cell law, explicitly rewrites the two selected fields, marks large dictionary
components locally irreducible and aggregates only by list induction. No limit
was raised; no unchanged failed source was rerun. Other failures so far concern
explicit carrier instances, slice-length views, entry counter normalization or
Result-map aliases. Per-attempt receipts retain status, wall, RSS, swap, exact
source revision/blob/SHA, dependencies and original axiom output.

## Remaining work

The claim's arithmetic producer association and the inactive sum must be
composed around transcript tags 27 and 28. Then PrepareOperations47's precise
q1/w1/c0bytes/transcript fields and domain map_err, FinishContext47 through
folded leaves/tree/root, second round, tag 30, final fold and queries; then
22 queries, six node multiproofs, publication indices and complete ordered
publish_compact bytes. The upstream backend.messages association must be
supplied from its actual caller, never assumed. RustRealRefinement and deployed
caller identification for disclosed/observerOracle belong to the still
prohibited step (4).
