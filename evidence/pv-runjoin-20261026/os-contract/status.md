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

`PV_RunJoin_OsFailureEndpoint.PV_RunJoin_OsFailure` composes the
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

`PV_RunJoin_SourceEndpoint.privacy_headline_from_source_inputs` is now checked
(receipt23462). Its runtime/body/account and boundary/sourceBody/draw are
constructed from the full emitted body and checked frame lemmas. Six explicit
proof fields remain: E1_V329, native_ledger_V337, byte_blind_V338,
kernels_V339, disclosed_V038, observerOracle_V038. This partial specialization
has SEVEN DATA inputs (world, policy, inputs, disclosed, oracle, ideal,
boundaryData); it does not attain the requested native 2 -> 0 reduction.

`LedgerHandleObstruction` is checked (23464): an unchanged source handle cannot
encode a fresh ledger update through a handle-only decoder, and a fixed pure
external dictionary cannot implement fresh=true then duplicate=false on the
same handle/nonce. This is an interface obstruction, not a native E2 failure
or a witness leak. A correct interpreter must thread the filesystem world.

The optimized native full-entry gate passed with `ct-host-prover`: both real
public fixtures returned Entropy under persistent process-only EIO, with one
account callback, zero hash calls and no reservation records at that point.
Then actual reserve_fallible returned true for fresh and false for duplicate,
last_error=None on both, retaining one durable record. See native-client/.
The earlier r1p-check-only build fails on &&[usize] at host_commitment.rs:257;
source was not patched. This feature difference is not deployment adoption.
No default/devnet/Pool ELF replay or same-public-witness measurement is claimed.

The original source, guard, bad event, simulator and observer remain unchanged.
Final attempt totals, commits and next deliverable are updated after focused
checks. None of the partial-interpreter results closes a whole native row.

## Source/effect continuation results

The full generic source caller now factors through the actual single reservation
callback. `BodyFootprint.caller` propagates arbitrary state invariants from that
callback. `LedgerWorldInvariant.caller`, `LedgerBody.native_ledger_shape`,
`LedgerBodyFrames.frames`, and `LedgerBodyStrict` retain the entered path,
source header and modeled history while framing provider/policy/client. The
candidate callback retains the exact native source Boolean and header, rather
than substituting a model result. Native IO/E2 association of its separate model
state remains a proof obligation. Its per-body `reservation` is not a single
witness-independent boundary reservation function.

V339 was inspected first: under E1 it is exactly uniform native density on the
completed coin carrier; an arbitrary supplied density cannot establish it. V338
is split into public fault schedule, initial-ledger independence, and causal
frame prefix. V337 splits no-entry frame from entered reservation update; the
full source handle is unchanged except `last_error`, so a handle-only decoder
cannot supply the effect world. V336 and V045 frame/source equations are
proved for the explicit partial constructor, without native dictionary, trace
or full observer installation.

The unconditional store-carrier continuation attempt failed: ExternalFuns.op12
can distinguish distinct closure carrier types. The residual law is pointwise
callback parametricity of map_err; it must be installed/proved with the actual
external dictionary. This is not evidence of a protocol witness leak. Failed
sources and diagnostics are retained only as evidence snapshots, not accepted
Lean modules.

Kani: 3/15 actual runs (1 guard pass, 2 unsupported dlsym failures; the third
run changed libc to the frozen pin). Twelve runs remain unused: unchanged
unsupported native paths were not rerun and no syscall stubs were introduced.
The full 89 Lean continuation attempts are accounted separately.

A read-only Kani-evidence scp after run03 was made without a fresh pre-transfer
reservation receipt; no capped computation followed that transfer. This also
fell short of the lead's literal pre-scp receipt rule. Subsequent archive
transfers require an explicit fresh receipt.

## Final focused audit and retention

`PV_RunJoin_StoreContinuationResidual.mask_error_closure_transport` is checked
with standard axioms under the explicit MapErrParametric field. The full
continuation/header projection is still open; its last failure is receipt23505.

The final audit23507 imports all 39 accepted new proof modules and repeats their
axiom queries. This is a focused cached import audit, not the frozen dependency
manifest or a release result. No implementation/release artifact changed.

A fresh read-only archive admission at approximately17:46 UTC was refused by a
new cross-stream quiet window ending18:15 UTC. No scp or capped host job followed.
All accepted local objects remain in tools/pv-runjoin-20261026/local-proof; no
cache or key cleanup was performed. Earlier host archives remain intact. Source
and evidence are committed; the local source/object hashes are retained in the
final cache inventory. Native test retained-ledger is not deleted.

Next deliverable: install/prove the actual map_err dictionary law and full
source/header projection, thread native filesystem outcomes into LedgerWorld,
and prove one public reservation function and L1/L2/L3 decoder association.
Then close the native fields in the original endpoint, resolve the owner model
choice, and perform the pinned dependency-closure replay/axioms audit.
