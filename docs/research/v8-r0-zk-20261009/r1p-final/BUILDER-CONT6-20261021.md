# Builder continuation 6 — D99 source route

Branch `codex/cx-builder-ref6-20261021`, base `5676c09df`.

## Stage 1: owned records, P6 composition

`BuilderRecordsReference.records` proves total execution of the actual
D90 extracted owned reference. Its closed record maps compute all fifteen
witness and five public fields, for arbitrary words and either variant.
No successful-result, admission, canonicality, loop, or array equality
hypothesis is assumed. The path and public nested loops are proved by
symbolic suffix induction, with completed-cell invariants; no 16,384-cell
normalization or large recurrence reduction occurs. `raw_owned` enumerates
only eight array positions. The reference preserves the input pair and
snapshot, and withdrawal produces zero recipient owner/salt.

`BuilderRecordsP6.FieldsEqual` names exactly the twenty field equalities
covered by D90's six indexed Kani verdicts. `route_records` composes those
with the kernel reference refinement. `route_banks` transports the entire
`BuilderBankExtracted.merged_banks` result through the record substitution:
merge-check flag, stable, late, and merged banks, including monadic errors.
It uses the existing axiom-free std adapters. This is full result equality
under replacement of the mapper, **not** yet equality of that bank function
with `WriterRefine.copyCellMerged`. That separate callee/Parts correspondence
is still required for `RustRuntimeJoin.raw_trace_eq`.

The P6 source equality is external certificate evidence under the named
Kani/CBMC and extraction trust boundary. `Route` is a Prop hypothesis, not a
kernel postulate; no theorem claims to prove Kani soundness. The ordinary
reference theorem itself has no P6 assumption. `normalized_trace` feeds the
computed records into the existing canonical field-normalization theorem;
WitnessOk and PubCorr are still explicit successful-source obligations.

`builder-cont6-p6-audit.py` validates the six retained successful solver
receipts and their complete field coverage. All current production source
pins agree. The old Kani harness file is a byte-exact 14,644-byte prefix of
the current file; later proof-only additions do not change those harnesses.
The certificate records this rather than claiming an identical whole-file
hash. No solver regression was rerun with unchanged inputs.

Env-J attempts 9248–9263 retain failed elaborations and corrected sources.
Final successes are 9249, 9251–9253, 9261–9263: seven modules, 26 theorem
audits, only propext/Classical.choice/Quot.sound, zero swaps, maximum final
wall 5.06 seconds and peak RSS 4,044,408 KiB. Exact targets, source revision,
source SHA, direct-import fingerprint, exit, time and axiom lines are in
`builder-cont6-attempts.jsonl` and `builder-cont6-p6-certificate.json`.
The task runner snapshots replacements under the ref6 branch name and uses
run-joint.sh with env J, -M7000, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64. No existing shared module was replaced in this
stage: all seven module names are new. No shipped crate file changed.

## Stage 2: successful-source admission

Pending.

## Stage 3: shipped runtime join

Pending.

## Stage 4: real execution coupling and release endpoint

Pending.
