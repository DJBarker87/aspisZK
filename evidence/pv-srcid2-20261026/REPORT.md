# Native premise-family source audit

Branch: `codex/pv-srcid2-20261026`; base `d385c8908f` (research).
**Target not yet established. V152–V154 remain REDUCED; zero endpoint rows removed.**
No frozen implementation, verifier artifact, observer, simulator, security
statement, native fixture fibre, or deployment endpoint was changed.

## Family disposition

All five exact field statements and before/after tables are in STATEMENTS.md;
25003 prints the elaborated structure and each projection in requested order.

| Family | Status | Exact remaining boundary |
|---|---|---|
| compile_call | OPEN | `∀ i, NativeInput.run (inputs i) = ok (.Ok (inputs i).compiled)`; pure callee/reference implementations and valid successful runs, then installed input/return selection |
| words | OPEN | actual full mapper P6 equality plus selected-input `PV_Src_RecordReference.Checked`; the unconditional raw mapper law fails at out=2^30 |
| publicCorr | REDUCED to native interface, pure sub-obligations OPEN | exact seven-field PubCorr of the returned record and selected compilation's public projection; original field unchanged |
| admission | REDUCED to native interface | original RspendPlus on that same selected record/public; no conservation, membership, append or sentinel weakened |
| row_call | REDUCED to native interface | `∀ j, transport j = PV_Src_Transport.row j` for the actually installed transport; historical callee certificate retained |

The native interfaces are assigned to pv-runjoin5. REDUCED here describes the
retained boundary, not newly removed premises. Missing implementations of the
pure Records and ExternalLinear callbacks are not treated as effects under
D188. No `inputs` installation or native fixture instance was present in this
worktree. A request for its concrete module/branch reference was issued while
independent source work continued; no reply was available at report time.

**PV_Src_Premises: 5 before, 5 after.** Field list:
`compile_call`, `words`, `publicCorr`, `admission`, `row_call`.
No fields were discharged, added, renamed, or substituted at the native endpoint.

## Proved and checked

* `PV_Src_RecordRangeObstruction.output_bound_required` and
  `reference_counterexample`: the actual extracted owned reference preserves
  out and returns successfully even at out=2^30, where WitnessOk fails.
* `PV_Src_RecordReference`: all-field nominal adapters, an explicit reference
  dictionary invoking that extraction, its exact returned record, and WitnessOk
  from primitive checked-input conditions. This dictionary is not globally
  installed and does not certify the shipped mapper or actual empty-root helper.
* `srcid2-native3`: optimized native diagnostic importing the exact immutable
  mapper, pair_trace, poseidon2 and spend files by path, with original
  dependencies and no stubs. CopyRecords::new and banks return successfully;
  raw output at merged[10][1010] equals 1073741824. This is a finite checked
  source-domain counterexample to unconditional raw-callee range correctness.
  It is not a counterexample to a valid release fixture or outer wrapper,
  a successful full compiler execution, or a P6 shipped/reference equality proof.
* `PV_Src_NativeFamilyAudit`25003 checks the unchanged original
  `PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises`, both existing native
  conditional consumers, both existing canonical public fixture fibres and
  their successful extracted bank/column runs. There is no smaller native
  instance to test. Full native fixture inhabitance remains OPEN.

## Validation receipts and budget

| Target | Exit | Wall | Peak RSS / cgroup peak | Swap |
|---|---:|---:|---|---:|
| RecordRangeObstruction25000 | 0 | 1.91s | 4,086,472 KiB RSS | 0 |
| RecordReference25001, projection diagnostic | 1 | 1.98s | 4,090,312 KiB RSS | 0 |
| RecordReference25002 | 0 | 1.96s | 4,109,752 KiB RSS | 0 |
| NativeFamilyAudit25003 | 0 | 1.69s | 4,228,412 KiB RSS | 0 |
| Kani1 jobs/output conflict, ruled waste | 2 | 0.033s | raw receipt | 0 |
| Kani2 actual scalar check | 124 | 240.002s | 3,354,898,432 bytes cgroup | 0 |
| Kani3 MIR optimization diagnostic | 124 | 240.002s | 3,005,779,968 bytes cgroup | 0 |
| native3 exact-source boundary diagnostic | 0 | 0.457s | 162,972 KiB RSS | 0 |

Lean: **4/100 attempts**, 3 successes, 1 diagnostic failure. All current new
sources match successful receipts (`final-source-audit.json`). Every accepted
new theorem has only propext, Classical.choice, Quot.sound. Failed25001's
elaboration-generated sorryAx is retained as failure evidence and is absent
from the accepted final source/audit. No forbidden source proof construct or
raised proof option was introduced. No unchanged full manifest replay ran.

Kani: **3 intended verification invocations**, one ruled configuration waste
and two timeouts; **zero completed verifications**. Eight separate help/list/
codegen inventory invocations, including five failed inventory preflights,
are fully retained. Thus **11 total Kani CLI invocations**; even counting every
CLI invocation conservatively, 11/15. Harnesses were listed from actual
metadata before verification; exact name and empty stub lists are in
selected-harness.json / selected-harness-opt.json. The first verification
configuration failure stopped its queue; only after diagnosis was a corrected
single invocation made. The list command's macro-feature handling was
inadequate, so successful only-codegen metadata supplied the equivalent inventory.
No queue of guessed names was run. The timeouts supply no proof evidence.

Three release-mode native diagnostic invocations: two private-visibility
compilation failures (receipts retained), then the checked boundary execution.
All host commands have receipts in host-runs.json and individual directories.
Lean receipts include launch revision, source SHA and dependency fingerprint;
Rust/Kani receipts include command, launch revision, caps, wall, RSS, cgroup
peak, swap and axiom status N/A. Some new diagnostic sources were staged as
hashed overlays before their commit; the raw launch revision is retained
rather than silently rewritten. Exact source-tree association is given by
source-pins.json, sources/*.lean.txt and final-source-audit.json. The native3
source is committed at5527d5b6a2; its generated Cargo.lock atf32a69759b.
The executable is recorded only by hash and size in native-artifact.json.

All scopes used 6G high / 8G max / swap0. Own Rust/Kani scopes used TasksMax64;
the shared Lean launcher used the accepted TasksMax128 and -M7000. One own
scope at a time; fresh reservation receipts were taken. All capped work ended
before the user-specified17:45–18:15 UTC quiet window. No marker was modified,
no cap raised, no uncapped arithmetic job run, and no local target directory
created. No own capped scope remained active at collection.

## Stopping point and next deliverable

The common completion rule permits stopping on a checked source counterexample.
The attempted unconditional raw-callee range discharge has that counterexample;
it would be unsound to delete words on that basis. The three native-association
families stop at their exact interfaces as requested. Budgets are **not**
reported exhausted and no redundant verification was launched to consume them.
This branch does not complete the requested native family-removal campaign.

Next: pv-runjoin5 must identify its concrete installed input family, successful
outer-wrapper validation and returned compilation, and its selected transport.
Then prove the unstubbed full mapper P6 equality (including actual empty roots),
join `Checked` to those executions, construct both full native release fixture
runs and the canonical instance, and remove words only after those proofs.
Complete the pure compile_call/record/public obligations and RspendPlus transport
before the native BuilderPremises installation. Replay the frozen dependency
closure and axioms audit only after real endpoint premise removal.
