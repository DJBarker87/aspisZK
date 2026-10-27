# pv-srcid3 resumed result

Branch: `codex/pv-srcid3-20261026`. Base: `52a0f8acee` (research).
Resume head: `2311884064`. Target not yet established.
`COMMITS.txt` records the branch history; no push or merge was performed.

## Established and retained

Accepted new modules in this resume:

- CanonicalNormalize: withdrawal erasure preserves the original public and
  admitted relation; transfer witness unchanged.
- CanonicalTransferRecord: every private transfer record field equals the
  path-packed canonical witness, using the actual canonical request.
- PackedSelection: generalized from the draft's FrozenInput.Data to
  CheckedCanonical.Data, allowing arbitrary supplied snapshots. It preserves
  the public, packs all membership bits, proves Checked for every admitted
  canonical instance, and constructs a reference record plus WitnessOk for
  every root table. It does not assert bank or full compiler success.
- CanonicalWithdrawalRecord: admission determines the actual public withdrawal
  amount; private records equal the recipient-erased canonical witness.
- FocusedAudit: 153 axiom checks over the restored focused dependency cone,
  all subsets of {propext, Classical.choice, Quot.sound}.

All 60 current module sources added since the base match successful focused
receipts and standard reported axioms (resume-accepted-axioms-audit.json).
That receipt/source audit is not an all-branch kernel replay.

Actual deployed PV_Src_Premises: **5 → 5**. Existing selected fixed-root
reference: **5 → 3**, conditional on its retained Remainder. No endpoint premise
was removed, added or weakened in this resume. The unchanged BuilderPremises
consumer remains the original consumer; no newly instantiated full smaller
Remainder or endpoint installation is claimed.

## Per-family status

| Family | Status and exact retained boundary |
| --- | --- |
| words | REDUCED to full unstubbed shipped mapper = owned dynamic reference (`PV_Src_RecordDynamic.dictionary`) and installed canonical input selection; Checked on every admitted canonical encoding is DISCHARGED |
| publicCorr | REDUCED to canonical snapshot/root selection and the pure source equation `pair_empty_roots = ok PV_Src_CanonicalRoots.table`; the fixed-root reference theorem is retained |
| compile_call | OPEN: `∀ i, run (inputs i) = ok (.Ok (inputs i).compiled)`; owned ExternalLinear implementation was already supplied, pure Records association remains unverified |
| admission | REDUCED to the exact original `PV_Src_NativeIdentification.PV_Src_Premises.admission` RspendPlus statement on the returned record and selected public; the combined stronger bridge is unaccepted |
| row_call | REDUCED to `∀ j, transport j = PV_Src_Transport.row j` |

The read-only RunJoin pin is `3478e00a58970c2480a1b20451dc107cfb1ac98f`.
`PV_RunJoin_SourceEndpoint.inputs` remains a free family into
`PV_RunJoin_PureSourceLift.Inputs`; it does not install a PV_Src input selector.
Exact hashes and interface are in runjoin-resume-read-only.json. No foreign
worktree or soundness/ledger file was edited.

## Non-vacuity and failed draft

The prior transfer/withdrawal canonical carriers and primitive bank-stage
non-vacuity remain as previously proved. The new generalized selection has
constructive record-stage non-vacuity for every supplied canonical carrier,
including both fixture carriers. Full compiler-success/installed fixture
fibres remain OPEN; neither is inferred from primitive-stage success.
The stronger frozen-bank selection draft is retained separately and uncompiled.

CanonicalPrivateRecord is only an UNACCEPTED draft. 27438 failed to unfold its
wrapper in the withdrawal branch. 27439 checked its witness/admission proof
bodies and printed standard axioms, but the module exited 1: I added audit
checks for PackedSelection without importing it. The import is corrected
only in resume-drafts; no further Lean attempt was authorized. It is excluded
from the formal module tree and all accepted-result counts. The 27438
error-recovery sorryAx lines are retained, not accepted as a theorem.

## Verification, cache and audit limits

The restoration flag was absent until first observed/read at 22:08:24 UTC.
No host scope or Mac Lean compile ran before then. host-gate-checks.jsonl
records the ten-minute checks. The task's lean-objects directory was absent;
two historical snapshot objects existed but were not reused. Missing task
objects were rebuilt against restored aspis-joint-20261019 objects through the
unchanged launcher. The existing task Rust/Kani cache was reused.

Full FinalAudit 27431 was blocked at dependency preflight; no Lean scope ran
and it was uncharged. The final source inventory has 129 PV_Src modules,
549 theorem declarations and 575 axiom-check requests. The read-only inventory
still finds 92 missing objects among 470 research modules in that proposed
closure (final-missing-objects.json). The complete final kernel audit and
coherent release replay were NOT completed. DEPENDENCY-CLOSURE.md and its JSON
name each theorem's source imports; this is not a missing-axioms substitute.

Lean used every resumed attempt: **37/37**, giving **130/130 overall**.
Thirty-five resumed exits were 0; two were errors in the unaccepted combined
draft. Maximum resumed RSS was 4,114,632 KiB; all recorded swaps were zero.
The restored launcher used -M7000, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64. receipt-cap-correction.json records correction
of the client's stale historical TasksMax=128 annotation; no launch/cap changed.
Only one task scope ran at a time. No memory cap was raised.

| ID | Target suffix | Exit | Wall | Peak RSS KiB | Swap | Revision | Axioms |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 27402 | CanonicalNormalize | 0 | 1.64 s | 4090916 | 0 | 18c180a456 | standard |
| 27427 | CanonicalTransferRecord | 0 | 1.53 s | 4100392 | 0 | 030f4f4d03 | standard |
| 27430 | PackedSelection | 0 | 1.56 s | 4104956 | 0 | 030f4f4d03 | standard |
| 27432 | FocusedAudit | 0 | 1.53 s | 4082320 | 0 | 052d91aa6c | 153 standard reports |
| 27435 | CanonicalWithdrawalRecord | 0 | 1.58 s | 4104596 | 0 | 41ed89b339 | standard |

Targets have prefix `R1Z/PV_Src_`. attempts.jsonl and RECEIPTS.md contain every
attempt's full target, exit, wall, peak RSS, swap, revision, source SHA,
imported object hashes and complete printed axioms/errors. Refused reservations
were uncharged and retried after at least three minutes with fresh IDs/names.
Old IDs 25300–25599 were never reused; next unused Env-J ID is 27440, with
zero remaining Lean budget.

No shipped source changed under crates/ or programs/. Rust changes are in the
cfg(kani)-only harness module. No ELF rebuild or pin update was claimed.
No wallet key was created, removed or destroyed. No ROW counterexample was
found. The historical raw out=2^30 diagnostic is outside Checked and is not
used as a stop or a refutation of V152–V154.

One procedural deviation is retained in RESERVATION-WAIT-DEVIATION.md:
the public-record retry's scope started at 22:43:15 UTC, about 28 seconds
before the required full three-minute wait boundary. It was charged normally;
no cap or source was changed, and it will not be rerun unchanged. A local
pre-host timestamp guard now enforces future waits. This is not concealed by
other successful proof receipts.

## Final Kani result and stopping point

All **8/8 resumed Kani invocations** completed: two successful metadata
compilations and six timeouts (full dynamic mapper 300 seconds, then transfer,
withdrawal, private record, public record and path-cell decompositions 120
seconds each). All six verification jobs are unstubbed with unwind33 and
unwinding assertions. No new verification success, configuration failure, or
checked ROW counterexample occurred. No source-equivalence conclusion is
credited to these timeouts. The earlier completed ExternalLinear/common-validator
certificates remain historical evidence, not new replay results.

Commands/harnesses were listed before charging and source pins are in each
receipt. Actual Cargo compiler fingerprints confirm opt-level=3,
mir-opt-level=4 and MIR inlining; expected heavy time was CBMC symbolic
execution, not unoptimized arithmetic. All new run swaps are zero and all
eight task scopes are inactive (final-scope-state.log). The task's 1,643,251,807-byte
Rust build cache was removed after teardown under the disk-hygiene rule;
no key filename candidates were found. Receipts, source, metadata inventory
and shared restored Lean objects are retained. No identifiable open solver
temporary paths were found in the recorded own-scope process scan.

Stopping reason: **both authorized allocations are exhausted**, not vanished
host paths, a source-domain diagnostic, or an established privacy target.
The corrected combined bridge remains a draft and the complete FinalAudit
remains missing. Next concrete deliverable under a new budget: compile the
corrected CanonicalPrivateRecord draft at next unused ID27440; restore the
named missing dependency objects; run the exhaustive all-branch FinalAudit;
then discharge the full mapper P6 equation symbolically/compositionally and
attach the installed RunJoin input/public/transport joins. No unchanged failed
aggregate should be relaunched with larger caps. Target not yet established.
