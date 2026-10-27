# Source identification: resume allocation 8

Branch `codex/pv-srcid3-20261026`; allocation base `e0d5c21c56`. **Target not yet established. MERGE GATE v2: BLOCKED.** No push or merge.

All **60/60 Lean attempts** and **2/2 Kani runs** are spent. Lean:43 new proof modules and three final audit shards accepted;14 rejected drafts remain evidence only. The last three charged attempts were the single frozen full audit. IDs41500–41587 were consumed monotonically:60 compiles,27 reservation refusals and one SSH transport failure. Refusals were uncharged. Next unused ID:41588, within41500–41799. One additional Kani reservation refusal was uncharged and consumed no env-J ID. Work stopped on allocation exhaustion, without a checked ROW counterexample.

## Merge gate and recompiled objects

[MERGE-GATE.md](MERGE-GATE.md) and resume8-merge-gate-v2.json retain **925 PROJECT objects, three gaps**, and **5,640 EXTERNAL objects, zero manifest gaps**. The inventory is the prior gate union the final kernel closure, retaining the three prior audit objects. All6,562 current audit-input/audit-object hashes were rechecked unchanged after the audit (resume8-post-audit-object-check.json). The env-J and lake manifest bytes still match allocation7; Lean4.32.0, toolchain commit8c9756b28d64dab099da31a4c09229a9e6a2ef35.

Ruling(h) resolved all three modules through the authoritative import-source pin table. Every shared source still differs from research HEAD. Each module was STOPPED: no overwrite, no compile and no changed-input dependent replay for that module. Gaps remain **3 -> 3**. Both complete hashes are retained below and in resume8-shared-final-check.json.

| Module | Authoritative research SHA-256 | Shared source SHA-256 |
| --- | --- | --- |
| AspisFormal.V6PublishedTheoremInterfaces | `904f5e5b9b6b38b7b3009cbe755ae90c692cb88c2aa303f1abf3c212a152a37c` | `80610f3a492b3d6012a1d75c0efbaa0233d29eaed337345d2ab9d98364a5e3a3` |
| R0P.LogUpChain | `a9b0e52dd73026f356c16237d4b29527a70a479fc14cb0d59c178e1d94ff1fb6` | `89e6f1477c616f5ab887fec3a5479d29fd0f33c6c5d0283d263186fdee30f6bd` |
| R0P.SemRounds | `564b9026233a36736f524407f357b44e173173139e52b9c4c6effbd88335bfd4` | `84cd1819f182940e61a11d0f46154d493b65a439a0b7a6a0f18e5f738af71383` |

All46 accepted objects from this allocation are individually listed with source/object hashes, revision and dependency fingerprint in [resume8-recompiled-objects.json](resume8-recompiled-objects.json). These are43 new proof objects and three audit objects. No existing project source was replaced. Historical changed-input replay gaps remain explicitly historical; a hash link is not described as a dependent replay.

## Exact source progress and remaining cells

- `PV_Src_ExternalCopy.source`: complete Result equality of owned extracted external_owned with R0PoseidonCopy.external_linear for every U32[16] state. Symbolic block writes, raw U64 sums, overflow bounds, output lanes, field meaning and canonicality are proved.
- `PV_Src_PortFullRoundCopy.{initial,final_round}` and `PV_Src_PortInternalRoundCopy.source`: exact source-body/copy Result equations for canonical states and constants.
- `PV_Src_Port{Initial,Internal,Final}RoundStep.source`: actual source iterations retain every callback Result and callback-state change.
- `PV_Src_PortConstantInstance.{initial_source,internal_source,final_source}`: all three actual frozen4/14/4 constant groups instantiate the symbolic source round recurrences. Finite iterator and literal constant-canonicality premises are discharged. `PV_Src_PortTraceCanonical.{full,internal}` proves successful finite runs retain canonical arithmetic state.

Actual source-parent cells remain **0 -> 0/21**. The complete threaded permutation/merkle_node_compress_v3-to-nodeCompress bridge remains open. `PV_Src_RootCertificate.source_eq` still requires the initial and twenty adjacent parent equations at the SAME explicit dictionary. No literal table replaces the source helper.

RunJoin was read-only throughout. Final pin414d6fb38c publishes **21/21 mathematical nodeCompress parent cells** and `PV_RunJoin_RootModel.{frozen_literal,initial,parents}`. Every cell/table source matches its accepted standard-axiom receipt, retained in resume8-runjoin-all-model-cell-pins.json and the read-only receipts. Those model cells do not supply the missing actual source-parent equations. New source/no-op-callback predecessor code is pinned as published code; no missing whole-parent result is inferred. The new external P6 gate and E_shipped extraction adapter are retained separately; production poseidon2.rs is byte-identical across branches, without inferring whole-build profile identity.

## Deployed premises and exact missing interfaces

`PV_Src_NativeIdentification.PV_Src_Premises` remains **5 -> 5**, with the original deployed premises file byte-identical. No deployed premise was removed, added, renamed or weakened. All predicates still concern the same record returned by the actual constructor.

| Family | Exact interface / remaining obligation |
| --- | --- |
| compile_call OPEN | For every installed input i, `@PV_Src_NativeInput.run actualExternal actualRecords (inputs i) = ok (.Ok (inputs i).compiled)`. Installed native input, both error layers, successful return and selected-compilation association remain. |
| words REDUCED | `newRecords (inputs i) = ok records -> WitnessOk (wordWitness records.w)`. Manual mapper/reference equality is retained; complete deployed Records.call/R_shipped equality and installed Checked selection are missing. |
| publicCorr REDUCED | For that returned record, `PubCorr (wordPublic records.p) (mapPub (canonicalPublic (publicInput (inputs i))))`. Exact owned external/round groups are now proved; complete source parent refinement,21 source cells and deployed public/snapshot binding remain. |
| admission REDUCED | Same returned record must satisfy BuilderSpendRelation.RspendPlus for canonical public/lifted witness. Installed source selection, public binding and returned compilation remain missing. |
| row_call REDUCED | `forall j, transport j = PV_Src_Transport.row j`. The actual fixed endpoint and PV_RunJoin_NativeSelectedInputs.same_selected_compilation remain required. |

No R_shipped/complete shipped Records identification or installed compiler-return interface is published on the pinned RunJoin branch. Its owned RecordsReference remains a candidate; bounded partial mapper checks or timeouts do not replace the missing interface. See RESUME8-INSTALLED-INSTANCE.md. L1/L2/L3, E1/E2, actual RunJoin, proof-account client association, simE and the full observer are unchanged. No privacy endpoint premise was removed.

## Validation and receipts

Earlier draft manifests retain stage-time statuses; final acceptance is in resume8-new-source-check.json. Focused generic proofs and dependent bridges preceded one frozen full audit. Generator --check passed. All43 proof modules were individually accepted before the audit. The source scan finds no forbidden declarations/proof forms, no resource-option overrides and no changes under crates/ or programs/. The new Rust harness is in the existing cfg(kani) reference module.

| Audit ID / target | Exit | Wall | Peak RSS KiB | Swap | Axiom reports |
| --- | --- | --- | --- | --- | --- |
| 41585 / R1Z/PV_Src_FinalAudit8A | 0 | 0:01.84 | 4241288 | 0 | 243 standard |
| 41586 / R1Z/PV_Src_FinalAudit8B | 0 | 0:01.78 | 4241144 | 0 | 242 standard |
| 41587 / R1Z/PV_Src_FinalAudit8C | 0 | 0:01.95 | 4275280 | 0 | 242 standard |

Exact audit source revision: `a1e46397a5447888d210ace73ca78f411071b41f`. All **207 proof modules /727 unique reports** passed; axiom sets are subsets of propext, Classical.choice, Quot.sound. Raw outputs, exact source snapshots and complete transitive import-object fingerprints are retained. No unchanged full regression was repeated.

[RESUME8-RECEIPTS.md](RESUME8-RECEIPTS.md) and resume8-attempts.jsonl give every target, exit, wall, RSS, swap, recorded HEAD and printed axiom result. resume8-revision-links.json explicitly identifies10 dirty-source runs: original receipts record worktree HEAD, while exact compiled bytes are the hashed snapshots. Every accepted snapshot is additionally bound byte-for-byte to a matching commit; dirty runs are not misrepresented as clean HEAD builds. The rejected final-round draft had the wrong result carrier; its corrected first accepted statement uses an explicit Result projection to the actual pair return. No accepted statement changed (resume8-final-round-carrier-correction.md).

Both Kani runs used an explicitly optimized profile, taskset0-3, unwind33, 6G/8G/swap0/Tasks64, and sequential scopes. Expected time was optimized compilation followed by named CBMC.

| Target suffix | Result | Wall seconds | GNUtime RSS KiB (wrapper proxy) | Cgroup memory peak bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| pv_srcid7_helper_prefix11 | TIMEOUT 124 | 900.003123 | 15296 | 5141737472 | 0 |
| pv_srcid8_helper_prefix01 | TIMEOUT 124 | 180.003633 | 15292 | 2610020352 | 0 |

The900s retry is the single retry permitted by ruling(i), changing timeout and CPU affinity from allocation7. After it timed out, the second run split the asserted output region to root0. Both still execute the full21-call helper. Neither timed-out comparison proves equality. No checked ROW counterexample was reported. Both metadata records have empty stubs and verified_stubs; all193 recorded source/build-input hashes per run match their exact commits. Rust has no Lean #print axioms (N/A). GNUtime RSS is a wrapper proxy; the aggregate cgroup memory peaks are retained, not mislabeled as aggregate RSS. Post-run Cargo.toml and Cargo.lock match this branch.

One SSH timeout stopped host launches; a read-only recovery check succeeded, then fresh IDs resumed through the barrier. No infrastructure repair or cap increase occurred. Both Kani scopes are inactive. All46 own cached Lean objects matched shared copies before removal;5,332,720 Lean-cache bytes and402,099,255 Cargo/Kani-cache bytes were removed after retaining metadata. Source snapshots/preimages and shared sources/objects remain. No exact owned /tmp solver path was identifiable after termination; unrelated temporaries were left. No wallet or account key was created or touched. See resume8-cache-cleanup.json.

## Next concrete deliverable

Reconcile the three shared-source mismatches under ruling(h), then compile the approved sources and required changed-input dependent closure before any CLEAN gate. For proof continuation, compose the now-instantiated round groups with the actual merkle-node no-op callback and state initialization, prove complete threaded permutation/merkle_node_compress_v3-to-nodeCompress correspondence, then apply the21 pinned mathematical parent cells to discharge the21 source cells and PV_Src_RootCertificate.source_eq. Separately obtain the complete deployed Records/R_shipped equation and installed compiler/input/public/snapshot/selected-compilation interfaces. Target not yet established.

## Allocation commits

`git log --oneline e0d5c21c56..HEAD`, captured through the pre-report revision, is in resume8-commits-before-report.txt. The final evidence/report commit follows.

```text
a1e46397a5 Freeze the complete source theorem audit after all focused targets pass
cf5cd692b9 Instantiate the symbolic round groups at the actual frozen constants
d2db8202e4 Qualify Result inversion with its defining Poseidon namespace
988619ec24 Resolve the Result inversion lemma for finite-round canonicality
a4e3bc4e8b Draft finite traces at the frozen round-constant arrays
ee3945f7ec Expose only the literal constant tables before bounded scalar checks
ce2fe5bb96 Correct the unaccepted final-loop draft to the actual result carrier
d4dec7b254 Record exact round-body and callback-preserving step refinements
d597d31545 Supply the explicit owned dictionary to source round equations
7f022c679d Record host SSH timeout and preserve unspent proof allocation
717e441796 Draft checked enumeration and owned array iterator traces
2fed2e0d29 Expose and compare the complete internal trace-step Result terms
bc714ef07a Resolve the extracted array iterator namespace in round steps
b73d5c4878 Draft canonical output preservation for finite trace rounds
6215637ead Validate complete owned external layer equality and nonlinear round models
bc35a5225d Pin newly published external P6 evidence and retain records association gaps
e3e018c342 Make finite iterator projections explicit and link proof snapshot revisions
8374857e63 Pin external model corrections and finite round composition candidates
7f491f7747 Validate external column sums and output-lane semantics
dfbc7320a6 Validate symbolic in-place block correspondence and retain exact receipts
6ddc8e0ea0 Draft symbolic external and round refinements pending host checks
7a4189c85d Split the timed out helper prefix comparison to the initial root
ba69eb0348 Draft symbolic block correspondence while the permitted Kani retry runs
86ed51d4b7 Record published owned records interface and retain installed association gaps
cbcac1bd08 Prepare bounded continuation clients with source mismatch stops and timeout ruling
61f92ac911 Retain three merge gaps after authoritative shared source comparison
```
