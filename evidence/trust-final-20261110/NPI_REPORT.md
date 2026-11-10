# NPI_ report: final trust and axiom audit of the replayed closure (gate rows 9, audit half, and 10)

Date 2026-11-10. Worktree codex/cx-trust-20261110 from research aceb08e73ed. Host workspace /home/dombarker/project-offloads/codex-cx-trust-20261110; the replayed closure was used by reference. Target not yet established.

This job edits no existing document. NPI_TRUST_INVENTORY_PROPOSED.md is a proposal for the lead.

## What ran

- Four capped Lean scopes out of a budget of 10, one at a time, all at 6G/8G with swap 0, TasksMax=64, `-M7000` (NPI_ATTEMPTS.jsonl).
  - L001 was a failed API preflight (`getUsedConstants` was renamed in v4.32).
  - L002 was a successful preflight on core Lean.
  - L003 stopped on Lean's own -M7000 limit at 7.2 GB, because its first version walked every constant value of the 879k-constant closure. It was not rerun unchanged and no cap was raised. The census was rewritten to read headers only, and the value-level user search moved to source text.
  - L004 passed: 5.6 s, 7,007,392 KiB, swap 0, exit 0.
- No Kani and no extraction.
- Reused without rerunning: the L187 final artefacts. The four REACHABLE lists were re-hashed and match their sidecars and L187_AX2_SUMMARY.json. Also reused: TAS_G0_AUDIT.json, the ledger30 JSON, the PCXD_ and NOX_ packets, and NPE_SHRAMT_CHECK.md (read from commit b7a8ad98847, because it is not in this sparse checkout).

## A1. Reachability of trust (NPI_TRUST_REACH.json)

How each row enters the theorems:

| Mode | Rows |
|---|---|
| Kernel binders | S2TrustedSdkBorrow (`borrow`), TrustedStd (`std`, which also constrains `copy`) |
| `run.frame` (`NOC_Run5bHost.retained`) | RuntimeEntrypointAdmission ×2, RuntimePersistence. In deployed_charge these are inside the averaged event, not hypotheses. |
| Instantiated at the top | P1, RuntimeSyscall, Allocator, both AeneasExtraction structures |
| Window laws of the reached (bn) fissions | RuntimeClockSlotBinding, RuntimeReturnDataClear |
| META (on the deployed path, but their certificate roots TX2:219/TX2:226/TX1:327 are not in the cones) | RuntimeReturnData, RuntimeMemcmp, RuntimeSha256Value |
| Tool / ledger | D188, P6, NativeContractSemanticTransport, P7, AllocatorABICompilerSourceToELF, R22 |
| Constructed, never assumed | Historical CheckpointVersionBinding |

The following are UNREACHED and kept: RuntimeCpiAccountView, RuntimeEntrypointAdmission-Pool, the six POOL reviewed transcriptions, RuntimeCpiReadonlyEntry7, FixturePdaRuntime, and NMN-TX2:064. One item counts as reached only through a shared root: ReviewedTranscription-queries_from_pairs reaches the cones only because `AspisR1.RPx_Deployed.deployed` is listed among TX1:168's roots.

Reviewed transcriptions:

- The six named verifier items are reached.
- Of the 37 inventory entries (36 plus batch_tree), 9 are reached.
- The other 28 are NOT-IN-CONE: neither the item root nor any root of its rows is in either cone. They are kept, and they are not claimed to be unused association trust (see finding F2).

Structural finding F1, ledger rows against the cones:

- 140 of 599 CLOSED rows have a root in the cones.
- 7 more (TX1:330/333/344, TX2:213/221/240/241) enter through restated top fields (`NVR_TAS.*`, `NVR_TasRoots.*`, `NNT_Field.r241`).
- 450 rows' root theorems are in the closure but in neither cone.
- 2 rows (TX1:059, TX2:040) have no recorded root (NKT-F3).

This contradicts no row. It does mean that "599 CLOSED" is not "599 rows the Lean proof uses": for most rows the CLOSED certificate is association evidence, not a kernel dependency. AGENTS §3/§8 requires the published claim to say so.

Finding F2, a question for the lead and not a counterexample. For the 28 NOT-IN-CONE items, the frozen functions (for example `qm31_accumulate_product_channels`, `decode_pool_identity_v1`, `decode_checkpoint_box`) have no same-named model in the cones. They may enter through installed `AdapterRw.Ops` operations or RSL abstractions; `AdapterRw.Ops` has 54 constants in the cones (PROPOSED-HM-N). Whether those installed models rest on these certificates is the association question the provenance campaign and L188 must settle per function. NPI_ did not settle it.

## A2. One-to-one reconciliation

NPI_TRUST_INVENTORY_PROPOSED.md has the following parts:

- **A:** every reached row with its exact statement, how it enters, the constants, a removal condition and the owner record.
- **B:** the reviewed transcriptions, with a per-item removal condition for all 36 unnamed items and for batch_tree.
- **C:** the UNREACHED rows, kept.
- **D:** the PROPOSED rows, separated. These are HM-A SDK type models, HM-B slice iterator, HM-O cross-crate constant encoding, HM-L ShrAmt (recommended as a discharged verified bridge with its restriction), R22 CheckedVsWrapping, and NOX_ lines D.1 to D.7, plus the other PCXD classes listed by name.
- **E:** four stale ledger records.

New removal conditions were written for S2TrustedSdkBorrow, TrustedStd, RuntimeEntrypointAdmission, RuntimePersistence, RuntimeSha256Value, NativeContractSemanticTransport, RuntimeReturnData and ReviewedTranscription-polynomial. Some are "none available" or "none for the tool" where that is the honest answer. The 36 unnamed reviewed-transcription items also each got one.

Rows added under the standing delegation (2026-10-28 onwards), with their owner record from C3-BIN:

| Row | Owner record |
|---|---|
| RuntimeReturnData, RuntimeMemcmp | **owner accepted 2026-11-04** |
| RuntimeClockSlotBinding (11-05), RuntimeReturnDataClear (11-06), RuntimeEntrypointAdmission-Pool (11-07), RuntimeCpiAccountView (11-10) | added under the owner's 2026-11-04 class authority and reported; **no individual confirmation recorded** |
| FixturePdaRuntime (10-28 late) | **not confirmed** (non-vacuity only, unreached) |
| All ReviewedTranscription items from (ah) onwards | the class is owner-approved (amendment fifth, option A); **items individually unconfirmed** |
| CheckedVsWrapping | recorded in the claim draft 2026-11-09; **not owner-decided** |

## A3. Axiom audit of the final closure

- **Roots print standard axioms** (from the L187 final artefacts, not rerun). `#print axioms` gives [propext, Classical.choice, Quot.sound] for deployed_splitB, deployed_charge, fail_sub_rec and NNH8_DeployedOuter (final/combined.log; L187_AX2_*/stdout.log).
- **Raw walks are standard.** The pinned NNM_ProofDriver gives walked = collected = {Classical.choice, Quot.sound, propext} for all four roots. The cones have 146,370, 146,551, 146,371 and 146,377 constants, and are byte-identical to run 7.
- **Closure census** (NPI_L004, out/NPI_out_axioms.tsv). The closure has 19,862 modules and 879,350 constants, with 108 axiom declarations.
  - 3 are standard, and all 3 are in both cones.
  - **105 are nonstandard, and none of them is in either cone.** The set is identical, name for name, to CIa_UnrecordedAxioms.tsv of 2026-10-27, so run 7's figure is re-established on the replayed closure.
  - 84 of them are Aeneas formatter `_native.decide` axioms: 48 in AspisR1PublicPreparation.Funs, 18 in AspisR1RecordParser.Funs and 18 in AspisR1PrefixAggregateParser.Funs.
  - The other 21 are infrastructure:
    - 12 in Init.Prelude and Init.Core: sorryAx, lcProof, lcCast, lcErased, lcUnreachable, lcVoid, lcAny, isScalarObj, Quot.lcInv, Lean.ofReduceBool, Lean.ofReduceNat, Lean.trustCompiler.
    - 9 in Aeneas: Std.String get_target and get_target.spec, Core.Pin ×2, Core.Atomic ×2, Core.Panic, Tactic.Step.StepArraySpec native_decide, and Command.Decompose.TestsRec.recAxOp.
  - F-AXIOM stands: there is no reachable nonstandard axiom, but strict import-wide standard-only still fails.
- **No sorryAx.** The cone walks show none. No credited-module replay log shows one (L187 report §7). A closure-wide sorryAx user search was not repeated, because it needs a full value traversal and is the L003 shape.

## A4. Statement audit cross-check (TAS_G0_AUDIT.json against claim §1.3/1.4)

These binders are listed and correct: queries, run (frame, trace, ok1, out1, ok2, out2), the admissions and persistence inside frame, std, allocation217, allocation234, ch, alloc2, fx, w, H, wOf, anchor, and alloc1 (instantiated). Discrepancies:

1. **`L0 : S2Trust.Library W (Nat → Record)` and the type binders `{W Tx}`** are kernel binders of both theorems but are not listed in §1.3 or §1.4. They are universal data, constrained only through `borrow`.
2. **`copy`** is a kernel binder of both theorems. It is mentioned only in §2 ("Unchanged … copy") and is absent from the §1.4 table. It is universal data constrained by `std`.
3. **Naming.** The kernel binder is `borrow`; §1.4 and §4.3 call it `sdk`. §1.4 should quote `borrow`.
4. **`fx` has twelve fields**: pda, clock, reservation, indexError, root, length, prior, words, D, a, Q0, Q1. §1.4 lists only fx.a. `fx.pda : List Bytes → B32 → Option B32` and `fx.clock : Except ProgramError UInt64` have no headline counterpart: the headline's environment components were inside the universal `missing`. Both are universal Fixed data, so they are not restrictions, but they must be listed. §1.3's `missing` row should say that `missingLit` is taken at `envInst H fx.pda fx.clock fx.reservation`. The clock representation note in TAS_G0_AUDIT `owner_visible_verbatim` is not reflected in §1.3. Clock-independence is proved (`NNH8_Exec.clockFree` is in the cones).
5. **Type binder `CoreError`.** The headline has `{W A CoreError Tx}` with `indexError : CoreError` and `missing : Uninstalled CoreError`. After the change, `fx.indexError : NFN_NEW_GeometryDictionary.CE`, so CoreError is instantiated. §1.3 lists `A := Bool` but has no row for `CoreError := NFN_NEW_GeometryDictionary.CE`. The justification (the installed configuration's core error type) needs to be written.
6. **deployed_charge has no `run`, no `w` and no top-level `H` binder.** `Runs` occurs only inside the failure indicator, and `wOf` is arbitrary. §1.4 presents one table for both theorems; it should say that `Runs.*`, the admissions and RuntimePersistence are hypotheses of deployed_splitB only, and are parts of the event in deployed_charge.
7. **`queries` is quantified over two oracles.** Its exact form is `∀ J K, (issued (… envInst J …) … (normalize fx.a) K).length ≤ Q0+Q1`: the bound must hold for every environment digest J and every query oracle K. This is recorded in `written_confirmations` but §1.4 should quote it.

No hidden Root0, Realizes or injectivity hypothesis was found. The written confirmations in TAS_G0_AUDIT agree with the printed text.

## A5. Gate status

**Row 9, audit half. Axiom part: MET.** The roots and the raw walks are standard on the replayed objects. The 105 nonstandard axioms present in the closure are listed with their modules, and none is reachable.

**Row 9, trust part: audit done, not MET.**

- Reachability is established row by row.
- Four stale ledger records are identified (inventory §E).
- R22 is OPEN.
- The NOX_ realization lines and the PCXD hand-model classes are PROPOSED and undecided.
- The Pool ELF mismatch (121f3e29 against frozen e0e49c34) is untouched.
- Row 9 as a whole stays OPEN, because R22 and the Pool remain.

**Row 10: NOT MET.** A one-to-one proposal exists, with a removal condition for every row and per-item conditions for all 36 unnamed reviewed-transcription items. Remaining:

1. The lead adopts §4 from the proposal.
2. Owner confirmation, or rejection, of the class-authority runtime rows (RuntimeClockSlotBinding, RuntimeReturnDataClear, RuntimeEntrypointAdmission-Pool, RuntimeCpiAccountView), FixturePdaRuntime and the individually unconfirmed ReviewedTranscription items.
3. Owner or lead classification of every PROPOSED row (HM-A, HM-B, HM-O, R22, NOX D.1–D.7, and HM-C to HM-N), with HM-L recorded as discharged.
4. An answer to F2 for the 28 NOT-IN-CONE items.

### Proposed text for claim §4 (replace the opening paragraph, then add the rows)

> Authority: design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md as approved and amended, and ledger30 (NNN_LEDGER.json, 25 trust rows, 40 reviewed-transcription entries), reconciled one-to-one against the L187 replayed cones by NPI_ (evidence/trust-final-20261110, NPI_TRUST_REACH.json). "Used" names how the row enters `deployed_splitB`/`deployed_charge`: as a kernel binder, as a conjunct of `run.frame` (`NOC_Run5bHost.retained`), as an instantiated structure, as a window law, through a CLOSED row whose root or restated field is in the cones, or as the physical reading of a call on the deployed path (META). 140 of the 599 CLOSED rows have a root in the cones and 7 more enter through restated top fields. For the other 450, the CLOSED certificate is association evidence, not a dependency of the Lean proof. Rows the cones do not reach are kept and marked UNREACHED. Rows proposed by campaigns but not decided are listed separately as PROPOSED.

- In §4.1, add "Removal condition" to RuntimeSha256Value and to RuntimeSyscall, as in inventory A.1.
- In §4.2:
  - Change the Used column of RuntimeEntrypointAdmission and RuntimePersistence to "conjuncts of run.frame (NOC_Run5bHost.retained); hypotheses of deployed_splitB, parts of the event in deployed_charge".
  - Add the removal conditions of inventory A.2.
  - Mark RuntimeCpiAccountView, RuntimeEntrypointAdmission-Pool, RuntimeCpiReadonlyEntry7 and FixturePdaRuntime as UNREACHED.
  - Mark RuntimeReturnData, RuntimeMemcmp and RuntimeSha256Value as META.
  - Change "No CLOSED use yet" for RuntimeReturnDataClear to "window law of TX2:240 (FIN_240), reached".
  - Add a Confirmed column with the C3-BIN records of inventory A.2.
- In §4.3:
  - Rename the `sdk` binder to `borrow`.
  - Add the removal conditions of inventory A.3/A.4 for S2TrustedSdkBorrow, TrustedStd and NativeContractSemanticTransport.
  - Add the TrustedStd (Port1) line: not reached as a hypothesis.
  - Replace the "Standard logical axioms" removal text with: "None. On the L187 replayed closure (879,350 constants, 19,862 modules) there are 105 nonstandard axiom declarations, the same set as 2026-10-27 (84 formatter native_decide, 21 Lean/Aeneas infrastructure), and none is reachable from any of the four roots (NPI_L004)."
- In §4.4:
  - Replace the paragraph on the 36 items with the per-item table of inventory B.2, including its NOT-IN-CONE column and the F2 caveat.
  - Add the removal condition for ReviewedTranscription-polynomial.
  - Note that queries_from_pairs is reached only through `RPx_Deployed.deployed`.
- Add §4.6 "PROPOSED, not decided", with the table of inventory D.

### Proposed text for claim §6

Row 9, replace "OPEN in this row: the trust and axiom audit on the L187 cold-replayed closure, R22, and the Pool" with:

> Axiom audit on the replayed closure: MET (NPI_, evidence/trust-final-20261110). The four roots print and walk exactly propext, Classical.choice and Quot.sound. The closure holds 105 nonstandard axioms, the 2026-10-27 set unchanged, and none is reachable. Trust audit: reachability recorded row by row (NPI_TRUST_REACH.json). Still OPEN in this row: R22, the NOX_ realization lines and PCXD hand-model classes awaiting classification, and the Pool ELF (121f3e29… deployed against frozen e0e49c34…).

Row 10, append:

> Status 2026-11-10: a one-to-one proposal exists (NPI_TRUST_INVENTORY_PROPOSED.md), with a removal condition for every reached row and for each of the 36 unnamed reviewed-transcription items. NOT MET until:
> 1. the lead adopts it into §4;
> 2. the owner confirms or rejects RuntimeClockSlotBinding, RuntimeReturnDataClear, RuntimeEntrypointAdmission-Pool, RuntimeCpiAccountView, FixturePdaRuntime and the lead-added ReviewedTranscription items;
> 3. each PROPOSED row is classified;
> 4. the association status of the 28 NOT-IN-CONE reviewed-transcription items is settled (finding F2).

Rows 1.3/1.4: apply the seven corrections of A4. They change no statement; they make the listing match the kernel text.

Target not yet established.
