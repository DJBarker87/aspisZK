# OS failure contract continuation

Entry: `5090b732a0`, branch `codex/pv-runjoin-20261026`.
Target not yet established. Neither repair option is adopted.

## Statement inventory

`PV_RunJoin_OsFailure.FirstDrawFailure runtime r` names the exact interpreter
schedule: account callback at attempt zero succeeds with `(nonce,next)`, the
nonce check succeeds with `true`, and the next zero-initialized 64-byte fill
returns `((after,Err error),written)`. The record and the initialized world
have no witness argument. `execute_failure` returns
`ok (stop Entropy,{next with provider := after})` for every body/witness.
`witness_independent` compares the entire returned state and complete ROM view.
This is an interpreter theorem; native dictionary/observer installation is
not inferred from its name.

`outside_bad_iff` characterizes the UNCHANGED fuel-join bad event exactly:
all old parser events are false at `r.1.1`, no query guesses `r.1.2`, and no
fuel block in `r.2` is exhausted. An OS status is not a disjunct. An OS fault
alone does **not** prove these three conditions or source success.

`PV_RunJoin_OsFailureEndpoint.PV_RunJoin_OsFailure` is intended to compose the
exact reencoded source-success theorem, those three coordinate conditions,
and the named native error-log decoder equation. It must not be reported as
an existential concrete deployed counterexample.

## Owner repair choices (proposed only)

A adds `OsAvailable runtime boundary`: every in-capacity boundary draw on a
fresh zero 64-byte buffer returns `ok ((after,Ok ()),bytes)`. This excludes
OS-error status, interpreter failure and divergence at those draws; it says
nothing about E1, E2, nonzero seeds, or source association. The preparatory
availability theorem retains all eight endpoint premises, including V038,
and reproduces the endpoint conclusion verbatim. Its extra assumption is
currently redundant because the V038 fields remain hypotheses. Adding it is
not a discharge of V038 or an adopted deployment assumption.

B changes the model statement: a public `Option E` signal is supplied to BOTH
experiments. `none` runs the unchanged experiment, including the existing
simE ideal; `some error` gives both the same complete public failure view.
The failure-view function has no witness input. The observer still receives
the whole view, including bytes, side channels and oracle history. The fixed
signal error bound is unchanged; the failure-branch advantage is zero.
Native witness independence of that public signal and equality to the actual
native error view remain source obligations.

Recommendation: B, if the owner approves changing the model statement.
It represents a reachable ordinary kernel error and supports failure-inclusive
privacy without assuming perfect OS availability. A is appropriate only when
the deployment owner can justify the stated availability trust item. Neither
choice closes dictionary/effect, observer, E1/E2, or artifact association.

## Resource exception

Admission for 23421 returned `allowed=false` at 15:08:08 UTC. I erroneously
launched anyway. The shared launcher admitted the smaller inventory it uses;
that does not override the stricter required barrier. The capped scope
completed with a type-check error, peak RSS 4,251,252 KiB, swaps 0. This is a
procedural violation, not accepted resource-compliant validation. The next
admission request was after the required three-minute wait, at 15:11:23 UTC,
and was also refused; no build followed that refusal.

## Endpoint accounting

Runtime/boundary free data parameters remain 2 -> 2. Endpoint proof fields
remain 8 -> 8. No whole ledger row is closed. No source under crates/ or
programs/ changed, and no keys/accounts were created, used or cleaned up.

Runtime field list: world, account, body, disclosed, observerOracle, ideal.
Boundary field list: sourceBody, draw, law, frame, coordinates, nativeWeight,
ledger, reservation, schedule, unix, fault.

Final attempt totals, exact checked theorem inventory, commits and next
deliverable are updated after the focused checks.
