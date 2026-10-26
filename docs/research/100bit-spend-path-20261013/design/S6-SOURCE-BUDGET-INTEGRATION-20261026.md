# S6 complete source substitution and snapshot byte budget — 26 October 2026

Two enclosing/source-interface results are now checked. Whole S1/S2/S6 and the
per-attempt100-bit target remain OPEN. No enclosing trust/source premise has
been removed, and no native allocator instance has been invented.

## Complete source decoder substitution

`S6CurrentDirectDecoderV1.lean` proves `decode_eq` on the COMPLETE Result,
including outer fail/divergence and the exact SDK InvalidAccountData mapping.
The right side invokes the original concrete AspisR1TerminalDecoder decoder,
with the existing full nominal-carrier bijections. No successful decoding,
canonicality, independent child output or accepted caller is a hypothesis.
`decode_total` reuses the checked original decoder TOTAL theorem at its
extracted-source interpretation, not as native allocator or SDK TOTAL.

`install_eq` proves equality of the COMPLETE installed Ops dictionaries.
`stage1_eq` consumes that equality in the WHOLE actual emitted stage1_owned
computation on the same program/accounts/data. `first_decoded_eq` similarly
preserves the complete first_decoded call. All other operations are the exact
same retained dictionary; neither the account carrier nor the SDK body is
simplified or replaced. The equality changes no call order, adds no decoder
execution and does not substitute the re-decoding firstCurrent for the actual
single-decoded first_decoded route. It is an extracted-source result, not a
new source-to-native/runtime/ELF or adaptive-experiment transport theorem.

Before: the earlier success consumers invert decoder success to identify the
same statement. After: the complete decoder-slot substitution and enclosing
stage1 equality hold for every source Result with no child-success condition.
The existing source-model success, full-field, pointer/length, error and same-box
native certificates remain available for composition. The standing actual
SDK/AeneasExtraction/library/runtime premises are unchanged; this theorem does
NOT discharge them or instantiate every remaining adapter/verifier slot.

## Actual snapshot interface: range and totality

`S6SnapshotBudgetV1.lean` uses the EXISTING complete Entry and Allocator
interfaces and the original admittedSizes/reserve/allocateSnapshots definitions.
No account fields, errors, metadata or handles are removed. For EVERY Entry:

    sum(admittedSizes e 3 firstSizes) <= 58295 +1880 +1768 =61943.

Rejected lengths are included: the interface filters them from the reservation
list. This bound does not assume an accepted first call, valid proof, canonical
public data, correct metadata, distinct handles or successful allocation.

The concrete private-state reference `budget : Allocator Nat` interprets its
state as requested-byte capacity, consuming each request or returning outer
panic on insufficiency. `reserve_fits` and `reserve_insufficient` prove the exact
complete Result of that original reserve loop by symbolic List induction.
No large recurrence evaluation, native_decide, custom axiom or resource option
was used. `allocate_snapshots_headroom` consumes those laws in the original
allocateSnapshots helper: a262144-byte reference budget leaves at least200201
requested bytes, with the exact same complete account heap.

This is a SOURCE-INTERFACE requested-byte bound. It is NOT the deployed bump
allocator, not an actual peak-RSS/CU bound, and not a proof of all allocation
requests, alignment, allocator rounding, entrypoint/OwnedAccount Vec overhead,
public-decoder Boxes or later verifier allocations. Those omissions are explicit.

## Why snapshot success alone does not close native child allocation

`snapshot_success_not_child_admission` is a kernel-checked countermodel using
that SAME Allocator interface and the SAME admitted snapshot request list.
Starting with exactly the list's summed budget, snapshots return ok0; appending
one requested byte aborts. It proves that successful snapshot reservation alone
cannot justify a normal allocation in a child. It does NOT show the actual
fresh release heap is insufficient, that a deployed spend fails, or that the
existing conditional SDK theorem is false.

The source first wrapper explicitly reserves snapshot requests, then calls
`native program e.first data` WITHOUT passing private state, then cleans the
previous allocated state. `Allocator` has exactly `allocate` and `cleanup`.
A concrete source-to-runtime interpretation must therefore either justify
normal child allocation at the actual reachable initial state/footprint or
represent those effects in a sufficient caller interpretation. The range theorem
now gives a concrete starting inequality for that proof; it does not supply
unrepresented effects by renaming them as an already proved frame.

D188/D189 source/extraction and safe-container/SDK interpretations remain the
approved standing boundaries. They are pinned/read from immutable research,
alongside the accepted NP6 source certificate and its exact qualification.
This packet neither rejects that ruling nor silently expands the concrete
snapshot-only Allocator definition into a certificate for all child requests.
NP6's Claims-specific layout/content/cleanup gates are reused as methodology;
no Claims/S2/S3/S4/S5/S9 work or source was duplicated or modified here.

Next concrete obligation: pin the actual public-decoder allocation backbone,
its called allocation-free leaves, layout/alignment bounds and the actual
reachable fresh-heap prefix, then consume its headroom in the same source SDK
witness. Source inspection sees snapshot, afterstate, late, common, statement
and outer adapter Box construction points; that is a candidate backbone,
NOT yet a proved whole-call allocation count or native footprint. The S2 owner
retains the whole library/native caller association; S10 retains final lowering.
Any necessary model/source candidate must preserve errors/aborts/state effects
and needs explicit equivalence/re-pin obligations before adoption. No production
or model trust change is made here.

## Validation and pins

Accepted focused targets:

| Target | Attempt | Exit | Wall seconds | RSS bytes | Swap |
|---|---|---:|---:|---:|---:|
| S6CurrentDirectDecoderV1 | s6-current-direct-decoder-v3 | 0 | 45.593244917 | 2461450240 | 0 |
| S6SnapshotBudgetV1 | s6-snapshot-budget-v3 | 0 | 37.342371542 | 2331508736 | 0 |

All11 accepted #print axioms reports use subsets of propext/Classical.choice/
Quot.sound. Exact source revisions/hashes, selected import/object/tool pins,
commands and full logs are retained. Each job used the atomic local mkdir lock,
-j1 -M4400, and the smallest changed file. No dependency rebuild, unchanged
full manifest, Rust gate, extraction or SBF build was run.

Failed DirectDecoder v1/v2 and Budget v1 attempts are retained and EXCLUDED:
constructor/namespace resolution, a record-projection normalization before case
splitting, and folding the concrete budget dictionary before rewriting induction.
They contain compiler recovery sorryAx, not accepted source axioms. Budget v2
was green and is superseded by v3, which adds the actual allocateSnapshots
consumer. No accepted source has sorry, custom axioms or resource overrides.

`tools/s6-source-budget-20261026/check.py` checks both final sources/receipts,
reused source pins, immutable reviewed research snapshots and the failed-attempt
classification. Audit PASS; no compiler replay. Evidence is source-only under
`s6-source-budget-integration-v1`, plus the exact focused attempt directories,
`s6-source-budget-import-pins.json` and `s6-source-budget-audit-v1.json`.
No binaries or compiled objects are committed. Production remains unchanged.
