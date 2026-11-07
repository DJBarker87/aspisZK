# RSL Revision 2 impact on the merged NNC_, NNE_, NNF_ and NMV_ modules

Target not yet established. This record decides two things for every merged module that imports or restates a spec changed in rev2: whether it still compiles against rev2, and whether its statement still matches its TAS interface field. The changed specs are the owned getters, `verifierCheckpoint`, `S1Lib`, both `mapVErr`s, and RowSpec_241/240/221/213/344/333/330 together with their 345/328/242/233/234 children. Nothing here credits a row.

## Method

The modules are host modules. Where a module's import closure is local (RSL_, TCK_, TAS_, TFM_, EVB_ and sibling RSL-level modules), it was compiled locally against rev2: 31 modules, rev2_local_check.sh phase B. All others were decided from source, by reading every use of the changed names: `OwnedAccount.data`/`data_len`, `verifierCheckpoint`, `RS.ofExcept` at a getter site, `mapVErr`, `rejects_silent`, `S1Lib`, and any `unfold` of a changed Ref. Per-file exit, wall, RSS, swap and sha256 are in REV2_LOCAL_COMPILE.tsv, and axioms in REV2_LOCAL_AXIOMS.txt. Every file was below 0.7 GB, with 0 swaps.

## Decisions

| Job | Module | Compiles vs rev2? | Statement vs TAS field | Restatement |
|---|---|---|---|---|
| NMV_ | NMV_NoWritePool | **No** (verified: `free_steps` cannot discharge `OwnedAccount.data`, now `RS.ofCloned`, in the 234 branches) | unchanged | NMV_REV2_NOWRITE.patch: add `ofCloned_free`, `data_free`, `dataLen_free`, `verifierCheckpoint_free`, and add them to `free_steps` |
| NMV_ | NMV_NoWriteOwned | **No** (233 getter/checkpoint sites; 242's `ofExcept_free` at `proofAccount.data`) | unchanged | same patch: macro arms, plus `data_free` at the 242 `pdata` step |
| NMV_ | NMV_NoWrite241 | **No** (`ofExcept_free` at `acc0.data`/`acc6.data`; `error_free` lacks the `format!` alloc step) | unchanged | same patch: `data_free` twice, plus `rs_seq_free _ _ (lift_free _ alloc_free)` |
| NMV_ | NMV_G2Reference, NMV_TasRoots, NMV_CandidateRoots | yes, after the patch (verified, phase C) | `NMV_TasRoots.packet`/`NMV_CandidateRoots.packet` still have the exact type `TAS.NMV_Roots … (implementation I a1 a2)` | none |
| NMV_ | other 25 local modules (RslLaws…WeakFold, Stage1Frame, …) | yes (verified, phase B) | unchanged | none |
| NMV_ | NMV_Stage1/Stage2/Model/Total*/Snapshot/Carriers/NNCWeak (host) | yes (Aeneas carriers only; NNCWeak takes `RowSpec_241` only as a packet parameter) | unchanged | none |
| NNC_ | NNC_RSLReads | **No** (`ofExcept_return` on `read0`/`read6`, whose hypotheses are now `acc.data` = `RS.ofCloned`) | unchanged (`Cut.read0 : acc0.bytes = .ok proofData` still holds) | replace both with `RSL.TASRev2.data_return` (TAS_Rev2Support, compiled) |
| NNC_ | NNC_RSLAuth | **No** (`successful`: the `mapVErr` error arm now starts with `RS.lift Spec.alloc`, so `impossible` is a bind, not a `pure`) | unchanged | one extra `rsbind_return` step, or `RSL.TASRev2.mapVErr241_error_not_ok` (compiled) |
| NNC_ | NNC_ReaderCut, NNC_SelectedReader | yes, once RSLAuth/RSLReads compile (they use only those statements) | unchanged | none |
| NNC_ | NNC_SnapshotRep, NNC_R0Rep | yes (`snapAll`, `OwnedAccount` structure and `NMV_RslSnapshots.snapAll_facts` unchanged, verified) | unchanged | none |
| NNC_ | NNC_FirstCuts, NNC_SourceCuts | yes (`OwnedAccount.data` here is the AdapterRw Aeneas term, not RSL) | n/a | none |
| NNC_ | NNC_NMFPrime, NNC_CaseSplit, NNC_G1a, others | yes (`S1Lib` only as a parameter; the new field is invisible) | unchanged | none for rev2. **Option B restatement** (owner decision, not rev2): `NNC_BindingRoot.root0_or_rec_collision` (selector generalised + `selects`); `NNC_NMFPrime.Packet` gains `select`/`selects`, `charged` uses `select`, and a new assembler targets `RSL.EVB.NNC_NMFPrimeB … R` with `eventImage : charged p ↔ R.EventRec c` and `selected` also taking `R.SelectsPair c`. `NNC_CaseSplit` is not consumed by the B top |
| NNE_ | NNE_AcceptedCuts, NNE_RslOk, NNE_SelectedRoutes, NNE_SelectedContext | yes (verified) | unchanged | none |
| NNE_ | NNE_PhysicalAccepted, NNE_RslError, NNE_AcceptanceSig, NNE_RecordSig, NNE_Snapshot, NNE_Stage1*, NNE_RuntimeTrace, … | yes (they unfold only TX1_344/TX2_240.Ref, whose text is unchanged; TX1_345/TX2_241 Refs appear only as abstract hypotheses that A1/A2 supply) | unchanged. The meaning of `model` hypotheses follows the rev2 Refs, which NND_'s A1/A2 must now be proved against | none |
| NNE_ | NNE_TopSplit, NNE_PhysicalTop | yes | TFM form (`Outcome ∨ E_head`). **Superseded under option B** by TAS_TopB_NNE.top_splitB_counts/top_splitB_physical (compiled) | not consumed; no edit needed |
| NNF_ | NNF_Folds, NNF_TAS, NNF_Reify, NNF_Dispatch, NNF_Carrier | yes (they unfold only TX2_221/TX2_213.Ref, whose text is unchanged; 344/240 are abstract packets; `S1Lib` is a parameter) | unchanged; `NNF_TAS.roots` still has the exact `TAS.NMW_Roots` type | none |

## TAS_/TFM_/EVB_ and option B

TCK_WeakRoot0, TAS_Interfaces, TAS_Top, TFM_TopExact and EVB_EventB recompile unchanged against rev2 (phase A). No TAS field type changed. Their RowSpec names now denote the rev2 Refs, which is the intended meaning.

Option B with Realizes is TAS_TopB.lean:
- `top_splitB` instantiates `EVB.top_splitB_full` (both events E_rec) at `ctxB` (pair := the adversary's outputs; `realizes_by_construction` is `⟨rfl, rfl⟩`).
- `realizes_everywhere` shows the instantiation excludes no world.
- `deployed_charge` is the averaging step over every H with E_rec charged once.

TAS_TopB_NNE.lean gives the counts-route variant NNE_ needs. All compile with [propext, Classical.choice, Quot.sound] or fewer. The open host item is RZ-STATE (TAS_G0_BRIEF.md section 6).
