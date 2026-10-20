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

The actual `pair_trace::validate_common` is now extracted and compiled in
`BuilderAdmissionExtracted`. No production Rust or extracted function body
was edited. The raw Aeneas enum/function identifier collision is resolved
by a recorded identifier-metadata-only `PairLeaf` → `PairLeafCtor` rename
in the LLBC, without changing bodies or types. The accepted extraction
includes actual `aspis-core` functions. Its three missing std declarations
are supplied by `BuilderAdmissionStd`: Result.map_err and short-circuit
slice all/any, retaining consumed iterator index and mutable predicate state.
The latter have symbolic list proofs; no external declaration remains.
The imported discriminant attribute and a literal shift-count type are
adapted to env J. The generated file's existing limits are retained.

`BuilderAdmissionRanges.validate_common_ranges` derives input positivity,
input < 2^30 and membership index < 2^20 from successful execution.
`BuilderAdmissionCanonical` proves both actual canonical-digest validators
and the membership-sibling scan. `BuilderAdmissionCommon.common_facts`
derives canonical key, salt, all 20 membership siblings, both pair
commitments, and successful pair validation. No Rspend or soundness premise
is used. `BuilderAdmissionRecords.words_of_common_success` connects these
facts to the exact owned-reference records and discharges WitnessOk from
common success plus only output bounds and canonical super-root siblings.
Those last two checks occur in the forest caller and remain explicit.

Final focused attempts: 9265, 9267, 9269, 9274, 9280, 9282, 9284; 24 new
theorem audits plus the actual validate_common definition audit, all with
standard axioms and zero swaps. Exact commands/times/pins/errors are retained
in `builder-cont6-attempts.jsonl`, `builder-cont6-extraction.json` and
`builder-cont6-admission-adaptation.json`.

Full successful-source semantic admission is **not closed**. A new focused
forest-caller extraction leaves the shipped records body opaque, to be
supplied by stage 1's P6 reference route (the collector checks its absent
LLBC body), and likewise leaves the D90 certified lazy external layer opaque.
Charon passes; Aeneas reaches a different error at `spend.rs:126:52–126:63`
(`&mut hash_fields`), InterpUtils.ml:167. Isolating `derive_nullifier` with
Charon monomorphization clears that route's first diagnostic-name printer
assertion when the printer is disabled, then reaches the explicit unsupported
higher-ranked-to-free lifetime constraint at `spend.rs:136–144`,
TypesAnalysis.ml:970. No unchanged retry or cap increase was performed.
This is the new extraction frontier; it is not the shipped-records borrow.
The forest output with opaque declarations is not accepted as a certificate.

The separate semantic obligations are still digest-check correspondence,
public/frontier/empty-root correspondence, embedded RspendPlus including
append/carry and sentinel, and their connection to success of the two
complete public entry points. The new range/canonicality theorems do not
silently discharge those obligations.

## Stage 3: shipped runtime join

Pending.

## Stage 4: real execution coupling and release endpoint

Pending.
