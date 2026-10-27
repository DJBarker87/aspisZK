# Source identification: resume allocation 7

Branch `codex/pv-srcid3-20261026`, base `6f0741bb10`.
**Target not established. MERGE GATE v2 remains BLOCKED.** No push or merge.

All **100/100 Lean attempts** and **2/2 Kani verification runs** are spent.
There were 89 accepted Lean attempts and 11 rejected drafts; rejected reports
are not accepted proof evidence. IDs 40000–40127 were consumed monotonically;
28 reservation refusals consumed IDs but no compile budget. Next unused ID:
**40128**, reserved user range 40000–40299. The final three charged attempts
were the single frozen full audit. No unchanged regression or failed harness
was rerun. Work stopped on allocation exhaustion, without a ROW counterexample.

## MERGE GATE v2 and authoritative source correction

[MERGE-GATE.md](MERGE-GATE.md) and resume7-merge-gate-v2.json inventory
**6,519 objects: 879 PROJECT and 5,640 EXTERNAL**. Every external object is
individually linked to the env-J toolchain and package manifest revision.
All 209 imported Aeneas objects exactly match the pinned port's object hashes.
External manifest gaps: **0**. R1FirstFold is classified PROJECT, with its
research FirstFold.lean source and accepted EJR receipt, rather than EXTERNAL.

PROJECT object gaps are **48 -> 3**. Forty-seven original gaps were recompiled from
selected research bytes. The remaining original projection gap closes by the
lead's new ruling (h), which identifies the authoritative source as
`docs/research/100bit-spend-path-20261013/lean/NaturalProjection.lean`.
Its accepted EJR receipt 30200 binds the exact current source and object SHA.
The earlier reported two-goal failure belonged to the wrong historical
remote-evidence source. **ProjectionHEAD is closed; no repair or clone was
installed.** This correction supersedes the earlier projection claims in
RESUME6-REPORT.md and historical allocation-7 stage artifacts.

Ruling (h)'s authoritative import-source pin table also exposes four shared
source path discrepancies: `AspisFormal.V6PublishedTheoremInterfaces`,
`R0P.SemRounds`, `R0P.LogUpAssembly`, `R0P.LogUpChain`. None was compiled or
copied by allocation 7. Both paths and both hashes are in
resume7-source-resolution-correction.json; observed shared source/object hashes
are in resume7-resolution-shared-observation.json. Ruling (h) requires stopping
these modules without replacing differing shared files.

`R0P.LogUpAssembly` has an exact historical cache association in that same
authoritative table: source SHA ccd2282e... equals current research bytes and
object SHA 9639f23d... equals the current object. Its object provenance is
therefore linked, explicitly as a historical source/cache pin, not a new compile
receipt. The shared source path still differs and was left untouched. The other
THREE object associations remain blocked. Exact dependent cones are enumerated
in the gate JSON: V6PublishedTheoremInterfaces 483, SemRounds 394, LogUpChain 396.
These are provenance blockers, not demonstrated theorem counterexamples.

The source-pin correction closes all original 48 gaps but discovers three new
object association gaps; the aggregate is not represented as a clean gate. The audit
checks the actual object closure and axioms, not these missing source links.
Branch additions are distinctly pinned reviewable candidate bytes, never
misrepresented as already present at research HEAD. Final comparison of all
776 existing selected sources, using authoritative paths where available,
found no byte changes since the research pin. See
resume7-current-head-comparison.json for exact revisions. Of the original
99-module changed-sampler cone, 23 modules were replayed, including the seven
outside the former projection cone. No full changed-input replay is claimed;
pending modules and reasons are listed in resume7-sampler-dependent-status.json.

## Family status and deployed premises

The deployed `PV_Src_NativeIdentification.PV_Src_Premises` remains **5 -> 5**,
byte-for-byte unchanged from the allocation base. No deployed premise was
removed, added, renamed or weakened. All record predicates concern the same
record returned by the actual constructor.

| Field | Exact retained interface / result |
| --- | --- |
| `compile_call` OPEN | For every installed input `i`, `@PV_Src_NativeInput.run actualExternal actualRecords (inputs i) = ok (.Ok (inputs i).compiled)`. Both error layers remain. RunJoin's payload transition does not supply compiler success or the actual dictionary association. |
| `words` REDUCED | `newRecords (inputs i) = ok records -> WitnessOk (wordWitness records.w)`. `PV_Src_MapperBody.{witness_eq,public_eq,call_eq}` prove complete Result equality for the explicit manual field transcription against the owned dynamic reference. `PV_Src_MapperWords.dictionary_eq` and `.words` prove candidate dictionary equality and checked word admission. Actual deployed `Records.call` equality and installed `Checked` selection remain missing. This is not the requested full shipped mapper equality. |
| `publicCorr` REDUCED | For the same successful `newRecords`, `PubCorr (wordPublic records.p) (mapPub (canonicalPublic (publicInput (inputs i))))`. `PV_Src_RootSourceEquation.{source,pure_source}` and `PV_Src_RootCertificate.source_eq` retain the actual root-helper equation and initial plus twenty adjacent parent equations at one dictionary. The 21 Lean cells, full external/permutation/parent correspondence and deployed snapshot/public association remain open. |
| `admission` REDUCED | Same returned record must satisfy `BuilderSpendRelation.RspendPlus` for the canonical public and lifted canonical witness. `PV_RunJoin_SourceSelectionContract.selectedRecord` and `PV_RunJoin_SelectedAdmission.Remainder.admission` still require the installed source selection/public binding. |
| `row_call` REDUCED | `forall j, transport j = PV_Src_Transport.row j`. `PV_RunJoin_InstalledTransport.endpoint_row_call` still requires the actual fixed endpoint and `PV_RunJoin_NativeSelectedInputs.same_selected_compilation`. |

The exact internal-layer completion is new:
`PV_Src_PortInternalCopy.source state canonical` proves complete Result equality
between actual extracted `poseidon2.internal_linear_lazy state` and
`R0PoseidonCopy.internal_linear state INTERNAL_SHIFTS` for canonical inputs.
The supporting 15-step symbolic recurrence, checked source-order sum,
no-overflow bound, canonicality and all 16 field-model lanes are proved in the
PortInternal/PortSum modules. There are 17 new accepted proof modules in total,
plus the three audit shards. Symbolic shape lemmas avoid large recurrence
normalization. This internal-layer result does not prove a full parent or
instantiate any of the 21 helper cells.

RunJoin's branch was consumed read-only, pinned through `07b86d...` (full pins
and reports retained). RunJoin11 publishes literal transfer/withdrawal public
records, transitions and public inputs, but no installed native Input/compiler
return association. RunJoin12's actual extraction fails closed on structured
Drop/destructor semantics; its adapter is uninstalled. Its 21/21 Rust parent
leaf coverage belongs to its own recorded source/profile. Field candidate
feature guards, the pair-trace addition and Cargo.lock differ from this build;
no whole-corpus byte identity is inferred. See RESUME7-INSTALLED-INSTANCE.md,
RESUME7-MAPPER-BOUNDARY.md, RESUME7-ROOT-STATUS.md and the source-boundary JSONs.

L1/L2/L3, E1/E2, actual RunJoin, proof-account client association, simE and the
full observer remain unchanged. No privacy endpoint premise has been removed.

## Validation and resource receipts

The frozen audit was compiled once, as charged attempts 98–100:

| ID / target | Exit | Wall | Peak RSS KiB | Swap | Printed axiom reports |
| --- | --- | --- | --- | --- | --- |
| 40125 / PV_Src_FinalAudit7A | 0 | 1.77 s | 4,237,112 | 0 | 220 |
| 40126 / PV_Src_FinalAudit7B | 0 | 2.15 s | 4,236,680 | 0 | 219 |
| 40127 / PV_Src_FinalAudit7C | 0 | 2.11 s | 4,269,092 | 0 | 219 |

Exact audit source revision: `4b1c1979659b12b796df9eb8de394feefb53ce5f`.
All **164 proof modules / 658 unique reports** passed; every report uses only a
subset of propext, Classical.choice, Quot.sound. Raw outputs and source/import
hashes are retained. The generator's --check passed before the audit. Source
checking found 20 new files (17 proof modules plus three audit shards), all
accepted at their exact current hashes, no forbidden declarations/proof forms,
and no changes to crates/ or programs/. The original deployed premises file is
byte-equal. See resume7-new-source-check.json and resume7-final-summary.json.

Both Kani runs were optimized, capped at 6G/8G/swap0/Tasks64 and sequential:

| Exact harness suffix | Result | Wall | Peak RSS KiB / cgroup bytes | Swap | Revision |
| --- | --- | --- | --- | --- | --- |
| empty_roots::pv_srcid7_helper_prefix11, unwind33 | TIMEOUT 124 | 180.003 s | 15,296 wrapper proxy / 2,860,482,560 | 0 | 0a8c5413f0 |
| poseidon2::builder_reference::pv_srcid7_internal_linear_copy, unwind17 | PASS 0, 514 checks | 84.361 s | 701,172 / 758,534,144 | 0 | acf4eb76a7 |

Kani has no Lean #print axioms (receipt explicitly N/A). Metadata confirms no
stubs or verified stubs. All 193 recorded source/build-input hashes in each run
match its exact source commit; the metadata also retains optimized compiler
flags. The prefix timeout proves no helper equality; after isolating a smaller
internal obligation, that different harness passed. No mapper Kani run was used.
The draft suffix harness remains published and unrun.

[RESUME7-RECEIPTS.md](RESUME7-RECEIPTS.md) gives every Lean target, exit, wall,
RSS, swap, revision and axiom result. JSONL retains full source and transitive
import-object hashes. The final env-J and lake-manifest hashes match the
retained environment (Lean 4.32.0, git 8c9756b28d64dab099da31a4c09229a9e6a2ef35).
The 89 own cached Lean objects were hash-checked against shared copies and
removed; the 401,457,484-byte own Kani target cache was removed after preserving
metadata. Shared objects, source snapshots and preimages remain. No owned
solver temporary path could be identified after termination; unrelated /tmp
files were not deleted. No wallet or account keys were created or touched.
See resume7-cache-cleanup.json.

## Next concrete deliverable

The integration owner must reconcile the four shared source path discrepancies and three object associations
without overwriting differing shared sources, then rebuild the approved modules
and affected dependent cones. The proof continuation is the actual deployed
Records mapper equation (the manual transcription is still a candidate), then
the full source external/permutation/parent correspondence and 21 symbolic
helper cell instances. RunJoin must publish the same installed native inputs,
dictionary equation and successful compiler-return/public/snapshot associations.
Only those interfaces can discharge the existing five deployed fields.
No privacy endpoint is claimed established.

## Allocation commits

```text
4b1c197965 Freeze the final audit and correct authoritative source associations
acf4eb76a7 Isolate the canonical internal source operation after helper comparison timeout
0a8c5413f0 Refine the actual internal linear layer to exact canonical copy results
e0d50b8a1e Partition unstubbed root helper comparisons by returned output region
9a8f8137c3 Prove source internal loop cells and checked suffix summation
9ed1987bc5 Pin new RunJoin records and retain the missing deployed compiler instance
7b8b9b55c3 Prove complete mapper transcription and candidate word admission
e75a239390 Close project source hash gaps under the D241 merge gate
```

The final evidence-only report commit follows these source/stage commits.
