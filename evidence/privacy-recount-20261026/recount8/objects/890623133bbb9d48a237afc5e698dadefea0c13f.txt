# NDO reconciliation

## Nonidentical sources first

The two forests are **not an import-only byte renaming**. Of 2,922 historical/replay pairs, 70 differ after exact import-token replacement. 47 differ only in comments/whitespace; 23 have phase/observer changes. `NDO_DUPLICATES.json` puts every nonidentical pair first and records both source and predecessor object hashes. `NDO_SOURCE_DIFFS.txt` retains every difference.

`S1SemanticPhaseV1` formerly exported `AspisR1PublicPreparation.verifier.Phase := FirstCaller.Phase`. Its replay replacement exports no such alias and imports `RPz7_PhaseIso`, which retains the old S1 carrier as `RPz7_PhaseIso.Phase`. The selected emitted producer owns a nominally distinct `verifier.Phase`. The other 22 substantive differences change observer argument types to the retained carrier; `FIr_FinishComparison` additionally transports producer observers with `observerToFirst` at its FinishModel call and proof application. `RPz7_PhaseIso` supplies explicit variant-preserving bijections, callback/observer/consumer round trips and evaluation lemmas. These are existing source transports, not permission to identify the nominal carriers silently. Arbitrary callbacks and adaptive execution cannot be transferred by acceptance equality. Release `none` observers still require their concrete selected-call/type checks.

The full list of 23 changed bodies is in the JSON (`body_equal_ignoring_comments_whitespace_imports=false`). No new equivalence or cryptographic discharge is claimed here. The frozen Rust source, headline and release contract are unchanged.

## Inventory and provenance

The predecessor graphs contain 12,712 headline and 15,068 witness modules. Name matching includes RPx/RPv/RPu/RPt/RPz8/RPz7/RPz4/RPz prefixes and flattened dotted module names. Exact comparisons preserve all bytes except complete import tokens. A separate weaker comparison identifies formatting-only differences; it is not substituted for byte identity.

2,846 available source/provenance hashes were checked against historical candidates (some modules have both checks). 76 historical pair entries have no available source pin in the inspected predecessor manifest and no currently available source file in its cache record. Those entries retain explicit repository source paths/hashes and object hashes, but their source-to-object provenance is unverified. The two available host sources differing from the current repository (`Op5T_Final`, `Op5T_SuccessAccepted`) are retained as text and used for the comparison; their differences are comments only. Source hashes do not by themselves certify compiled-object provenance.

## Retargeting plan and budget

`NDO_RETARGET_PLAN.json` gives dependency-first ordering for 3,118 affected witness modules after substituting all 2,922 pairs. This is substantially larger than the authorized 60 normal Lean attempts. Existing compatible headline modules are reused directly; no arithmetic certificate is intentionally recomputed. Only task-owned source/cache paths may be written. Both predecessor caches remain read-only, and the task cache is retained.

Status: source inventory and source preparation are complete, with the 76 source-provenance qualifications above. Focused validation is partial: five checks passed, one unchanged-statement check failed. The combined replay has not run. Target not yet established; release obligations 1 and 4 remain open.

Stage 2 source preparation: all 3,118 NDO_ copies now exist under `lean/`. `NDO_RETARGET_SOURCES.json` pins each historical source and generated source. Every non-import byte is preserved, except the requested root namespace becomes `AspisR1.NDO_Joint`. Source imports exactly match the mapped predecessor dependency graph (zero discrepancies). A source scan rejects new axioms, opaque declarations, sorry/admit/native_decide. These are **prepared sources, not 3,118 passing proofs**. The 17 sources missing from predecessor source records use existing repository Lean sources, explicitly recorded in the source manifest.


## Focused validation and exact obstruction

All six attempts used one admitted scope at a time, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000. Every admission had allowed=true AND exit 0. Every attempt had swap 0, and source revision `bc05e50bdc` plus its exact source hashes (new identity modules were uncommitted inputs at compilation, explicitly marked dirty). No timeout, memory kill or unchanged rerun occurred. The complete commands, limits, source/dependency hashes and axiom lines are in NDO_ATTEMPTS.jsonl and individual receipts.

| Attempt | Target | Exit | Wall seconds | Peak RSS KiB | Axioms |
|---|---|---:|---:|---:|---|
| NDO_L001 | NDO_JFm_Result | 0 | 2.347354 | 2605284 | none |
| NDO_L002 | NDO_JGi_FinishFields | 1 | 4.388749 | 3824824 | REJECTED: sorryAx diagnostic following type error |
| NDO_L003 | NDO_JHe_InstalledData | 0 | 3.426525 | 5363848 | none |
| NDO_L004 | NDO_JHe_FinalInstallation | 0 | 51.216727 | 5304340 | standard subset only |
| NDO_L005 | NDO_InstalledIdentity | 0 | 2.987556 | 5455604 | standard subset only |
| NDO_L006 | NDO_PhaseIdentity | 0 | 1.605599 | 3780320 | standard subset only |

NDO_L002 fails at line 29, before a valid public source theorem exists:

```
Application type mismatch: The argument obs has type
  Option (verifier.Phase → Result Unit)
but is expected to have type
  Option (RPz7_PhaseIso.Phase → Result Unit)
in FinishModel.finish R B D pub pre before challenges obs
```

This is not a memory problem. The failed diagnostic's sorryAx is **not accepted**, and no theorem/object from this failed attempt receives credit. Its exact source snapshot is retained. The dependency path from NDO_Joint to this member is in NDO_PHASE_OBSTRUCTION.json. The read r1p-common.txt rule 4 requires: “If a target statement is ill-typed or false, STOP that item, write the obstruction/counterexample in your report, and continue independent items.” The requested unchanged-statement import-only copy is therefore retained as a rejected draft; its observer type was not silently edited.

Independent `NDO_PhaseIdentity.retainedCarrier` checks the replay alias equals exactly the historical `FirstCaller.Phase`, with no axioms. `observerRoundtrip` reuses the existing callback transport (Quot.sound only); `noneToFirst` has no axioms. This supports a future explicit alias relocation preserving the historical carrier. It does not prove arbitrary adaptive-execution transport or equate it to the emitted producer carrier.

`AspisR1.NDO_InstalledIdentity.seed`, `.installed` and `.finalInstalled` PASS with standard axioms only. The last states exactly:

```
FIp_Install.configuration err
  (IDa_Deployed.deployedConfiguration (missing m) err r) r =
JHe_InstalledData.deployedConfiguration m err r
```

`missing` copies all six data fields explicitly. It is not a Prop supplying acceptance or native refinement. These checks establish the generic selected installation identity in the repaired owner cohort. They do **not** instantiate the full NDO joint witness with it or discharge a headline premise.

## Combined replay and remaining work

Prepared final target: `lean/NDO_CombinedAudit.lean`. It imports RPx_Deployed and NDO_Joint, prints both roots' axioms, and checks both root types refer directly to the same global S2W_D189Wrappers.first/second declarations. This target is **NOT RUN**: the unchanged witness dependency is ill-typed and 3,118 affected modules require individual re-elaboration, exceeding the 60-normal-attempt ceiling. Only three of those 3,118 modules have passing receipts; 3,114 are uncompiled and one is rejected. The two independent identity modules also pass. Attempts used: **6/60 normal; 0/1 agg16**. Unused attempts are not passing evidence.

The mapped source-graph union of the two roots is 16,060 modules, a static prediction only. There is no successful combined exit, wall/RSS/swap measurement, kernel closure count, or two-root axiom audit to report. The source graph is not substituted for a kernel replay.

The three lead agg16 runner hashes were checked against the inherited pins and checked again at end (NDO_AGG16_RUNNER_HASHES.json, NDO_END.json). The final 16 GiB allowance remains unspent and must be freshly admitted and pins rechecked immediately before any future submission; never rerun it unchanged after failure.

Next deliverables: explicitly reconcile the S1 phase alias in the unchanged-statement contract (or obtain a narrowly documented source-name adaptation), validate the remaining prepared modules under a sufficient per-module budget, resolve the 76 historical source-to-object provenance gaps, then run the sole combined replay and establish the concrete witness/configuration specialization in that shared environment. No release, native-code, runtime, ELF, Kani or security-contract obligation is newly discharged.

## End state

NDO_VERIFICATION.json passes offline source/evidence consistency checks. All prepared source hashes match their manifest; failed and uncompiled sources remain explicitly uncredited. No original proved source, predecessor cache, wallet, key or frozen implementation was modified. No push or merge. No live owned host process remains; the task cache is retained at `/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028`. No committed file exceeds 20 MiB; no binaries or compiled Lean objects are committed.
