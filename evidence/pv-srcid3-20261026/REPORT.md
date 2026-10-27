# Source identification, resume allocation 6

Branch `codex/pv-srcid3-20261026`, base `92d3db0b2f`.
**Target not yet established. MERGE GATE BLOCKED.** No push or merge.

All **100/100 Lean attempts** and **4/4 Kani runs** are exhausted. IDs were
allocated monotonically in 37100–37265; refusals/holds consumed IDs but no Lean
compile budget. Next unused ID: **37266**, within the user's 37100–37399 range.
The last three charged attempts were the complete axiom audit, once, split
into three disjoint report shards. No unchanged failed/killed scope was rerun.

## Merge gate and exact provenance gaps

[MERGE-GATE.md](MERGE-GATE.md) enumerates **6,499 imported objects**, using the
actual kernel import headers rather than only source import parsing. It records
each object's SHA and accepted source/HEAD SHA association or exact gap.
The companion resume6-final-merge-gate.json includes the full graph and lists.
There are **810 source/object hash links**, **48 project source/object gaps**,
and **5,641 external package/toolchain mapping or build-provenance gaps**.
These are not claimed closed by a passing axiom audit.

The actual research HEAD `R1NaturalProjection` source SHA is still
`41db583fe5032f1d5ca0757d98da80d34f6949983599d369560eaa3574c5a368`.
Its cached object was built from the materially different `add9c506…` source.
Focused attempt 37102 failed at source lines 28 and 58. After rebuilding its
direct dependency and changing its transitive inputs, the identically scoped
HEAD source was reviewed again as 37260 and failed on the same two goals.
Both failures and their rejected sorryAx reports are retained. No protected
soundness source was edited. The existing old object remains, explicitly
uncertified against HEAD; it is not silently attributed to research.

`PV_Src_ProjectionProofs` validates every HEAD projection statement with two
proof-body repairs and standard axioms (37107). The exact **unapplied** repair
is PROJECTION-REPAIR.patch. This new namespace does not repair the cached
R1NaturalProjection. The final graph has **167 projection-tainted modules**.
The broader changed-input cohort still has **1,851 unattested replays** under
the gate's conservative complete-input test. They are named individually in
the JSON and flagged in the table.

The pinned research revision was c16e7e7895b7…. Final comparison to
b18ac2c1ea3f195d4ef14bf02061498108704fdc found **zero byte changes in all 775
selected existing research sources**. Branch additions are separately pinned.
See resume6-current-head-comparison.json.

## Objects rebuilt and profile correction

resume6-recompiled-objects.json lists all **92 accepted outputs, 91 distinct
modules**, with exact input/output hashes, revision and axiom reports. Full
charged and rejected target receipts are in RESUME6-RECEIPTS.md and
resume6-attempts.jsonl. Replacements preserved pre-existing shared source/object
snapshots; new copies are in the existing job directory. No launcher, env/J,
reservation script, resource cap or foreign worktree was edited.

The missing-provenance pass respected every launcher duplicate-input refusal.
The dependent cohort used actual complete transitive import-object hashes,
with specific initial/current changed-input witnesses; no nonce was used.
Byte-identical import-only modules do not conceal changed transitive inputs.
The allocation cannot complete the whole dependency closure.

One profile-selection mistake was caught and reversed. The older EJR Fmt pin
26ac770d… contains the type axiom `core.fmt.Formatter`. Fmt 37136 is rejected,
and sampler 37146 passed Lean but failed axiom validation. Both new shared/own
outputs were quarantined; pre-existing objects were hash-checked and restored.
The existing research repair daeafff8… defines Formatter as Unit. It rebuilt
at 37205; the named 37209 carrier audit has **no axioms**. The client now
quarantines kernel-success outputs that fail the axiom/report validation.
Raw historical exits were not rewritten. See resume6-rejected-profiles.json
and resume6-quarantine-restoration.json.

## Proved source results and retained family interfaces

The new pure call equations cover arbitrary input/output/recipient/change/
snapshot/asset arguments and the **complete Result**. `PureCallEquation.call`
specializes the extracted owned-reference dictionary to the pure external
callback, preserving the actual root-helper Result. It neither assumes an
effect law nor identifies the still opaque shipped `Records.call` leaf with
that owned reference. No source-success claim is inferred from its name.

RootRecurrence.loop and RootSourceEquation.{source,pure_source} prove the actual
root helper is an initial parent call followed by twenty source loop steps.
RootCertificate.source_eq composes exactly the initial zero-parent cell and
all twenty adjacent target-parent cells into the actual `ok table` equation.
Those **21 hash cells remain obligations**; they were not replaced by a table
stub, global success assumption, axiom, or concrete recurrence reduction.

PortReduce, PortMultiply, PortAddition and PortField prove actual source
scalar equations, field meaning and canonical outputs. PortSboxStep and
PortSboxLoop prove both actual nonlinear loops symbolically, preserving all
untouched cells. PortTables proves exact frozen initial/internal/final table
association. External/internal linear-layer, full permutation/parent, and the
21 source hash-cell equations remain to be composed/proved.

| Family | Final status and exact retained boundary |
| --- | --- |
| compile_call | OPEN: `∀ i, @PV_Src_NativeInput.run actualExternal actualRecords (inputs i) = ok (.Ok (inputs i).compiled)`. The pure owned-reference `Records.call` complete-Result equation is proved; shipped dictionary association and actual selected compiler success are not. |
| publicCorr | REDUCED: `@pair_trace.pair_empty_roots PV_Src_ExternalReference.dictionary = ok PV_Src_CanonicalRoots.table`, plus the same selected compiler success, canonical snapshot frontier and deployed public/snapshot association. The new recurrence/cell composition does not discharge its 21 cells. |
| words | REDUCED to full unstubbed shipped mapper equality with `PV_Src_RecordDynamic.dictionary`, plus the installed checked canonical selection. No new P6 equality is credited. |
| admission | REDUCED to `PV_RunJoin_SourceSelectionContract.selectedRecord` and public binding, and `PV_RunJoin_SelectedAdmission.Remainder.admission` on those exact records. |
| row_call | REDUCED to `PV_RunJoin_InstalledTransport.endpoint_row_call` at the same fixed endpoint, retaining `PV_RunJoin_NativeSelectedInputs.same_selected_compilation`; no concrete deployment selection was inferred. |

Late RunJoin pin 38dd26a1e85ad8ac16e048ed983a1afe2a9b71cc was read only.
EndpointSelection.data is published, but still takes selected/publicRecord
families and the fixed-endpoint binding. SelectedSourceReduction still takes
actual dictionary equalities, selected canonical encoding equality,
compile_call and admission. These are conditional constructors, not installed
premise-free source instances. Exact sources/hashes are retained in
resume6-runjoin-late-pin.json and resume6-late-readonly-*.lean.txt.

**Deployed PV_Src_Premises 5 → 5.** Zero fields removed, renamed, added or
weakened. The prior fixed-root conditional Remainder stays 3; it is not a new
deployed smaller instance. Both full successful compiler fixture fibres and
the exact RunJoin installation remain open. L1/L2/L3, E1/E2, actual RunJoin,
client proof-account route, simulator and observer requirements are retained.

## Full audit, Kani and resource receipts

The complete final audit covers **147 source modules**, plus the metadata/old
and new audit roots, with **616/616 unique standard axiom reports**. Only
{propext, Classical.choice, Quot.sound} occur. These passing imports/axioms do
not establish an ordered coherent research-HEAD source rebuild.

| ID | Exact target | Exit | Wall | Peak RSS KiB | Swap | Revision | Axioms |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 37263 | R1Z/PV_Src_FinalAudit6A | 0 | 1.80 s | 4234508 | 0 | 888aa93f5e | 206 standard |
| 37264 | R1Z/PV_Src_FinalAudit6B | 0 | 1.83 s | 4234568 | 0 | 888aa93f5e | 205 standard |
| 37265 | R1Z/PV_Src_FinalAudit6C | 0 | 2.01 s | 4266752 | 0 | 888aa93f5e | 205 standard |

All Lean scopes: -M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64, one at a time. Maximum recorded RSS was 4,266,752 KiB; all recorded
swaps were zero. The accepted source SHA and full printed lines are in the
JSONL; failed reports remain rejected. No package-wide unrelated regression
or frozen release artifact suite was rerun.

The four new unstubbed full-mapper harnesses partition recipient present/
absent × selected first/second. Each compares all 20 fields and executes the
actual dynamic root helper on both sides. Every run timed out at 180 seconds:
**no verification success and no checked ROW counterexample**. No earlier six
timeouts were rerun unchanged. Metadata has stubs=[], verified_stubs=[],
unwind33, with unwinding assertions enabled. Compiler fingerprints show
opt-level=3 and mir-opt-level=4; all 142 Rust compilation inputs match branch
bytes. Heavy time was CBMC after compilation. Full-scope cgroup memory peaked
at 2,607,497,216 bytes; swaps zero. GNU-time's timeout-process RSS is not
aggregate solver RSS. No aggregate RSS is invented. #print axioms is N/A for
Kani, and no Lean equality was installed from these timeouts.

REFERENCE-GATING.md confirms the six files without in-file cfg attributes:
drop.rs/drop_iterator.rs inherit cfg(kani) from reference src/lib.rs;
records.rs inherits cfg(kani) from pair_forest_copy_builder.rs; glue_tree.rs
and glue_append.rs inherit that parent; records_reference.rs is gated by
cfg(any(kani,aeneas_ref)). None of those declarations uses cfg(test).
No shipped crates/ or programs/ source changed. New Rust code is only inside
the existing cfg(kani) harness module; no ELF rebuild/pin change is claimed.

All Kani scopes ended inactive. Own FD scans identified no solver /tmp files;
no unrelated temp files were deleted. The own Rust cache was removed after
metadata/input retention. All 91 remaining own Lean object copies matched the
shared bytes before scratch cleanup. Sources, shared objects, pre-replacement
snapshots and rejected-output quarantine remain. Neither cache had key filename
candidates. No wallet key was created, deleted or destroyed.

Stopping reason: **both allocations exhausted**, not a temporary resource
refusal or a changed release target. Next deliverable: the lead applies/reviews
the two protected projection proof repairs, rebuilds its entire dependent
cohort and closes the remaining exact source/object attestations. Then finish
the actual parent/hash-cell and shipped mapper associations and install the
same selected RunJoin inputs/public/snapshot/admission with both full compiler
fixture fibres inhabited. Target not yet established.

Branch history for this allocation is appended to COMMITS.txt. The final
path-limited handoff commit follows that captured history. No push or merge.
