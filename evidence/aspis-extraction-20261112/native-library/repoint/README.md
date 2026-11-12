# X5: re-pointing the Aspis model chain to the carrier-free library

Status: target not yet established. This is a refactor record. Nothing in it is a new proof, and no theorem is
newly established. The re-point is partial. Six of the seven carrier names are re-pointed everywhere in the chain.
`SourceInputs` is not, for the reason in "What could not be re-pointed" below. Check c is therefore not empty.

## Inputs

- Chain sources: `docs/research/future-version/lean/` on `future-version`. The "before" sources were taken by
  `git archive` at a48bc69af17adfec8091951f9a608ce755165e33. All 76 module hashes in `compile-before.tsv`
  equal the replay-c1 manifest hashes (`evidence/future-version-20261111/replay-c1/manifest.tsv`).
- Carrier-free copies: the soundness lead's base modules (branch `research`, commit 4ce1cc0e0ad, directory
  `docs/research/100bit-spend-path-20261013/evidence/pin2-replay-20261111/aspis-lib/`). The objects come from
  `~/aspis-lead-infra/aspis-lib/objs`, read by reference only. Their sha256:
  - AspisHonestBudgetBase 688bbad7456afc8fbb02bf7336b236cab44d530dbdd37696ca78b0b9106dc4ee
  - AspisLib_Guard a10f85596f6e0f2820bf7fdbed7f73f3951c86777ba3b88157b424b6c0b13a37
  - AspisLib_QueryAccounting 8a20ba2d01ade5b933d34adeab94424d6ce963e16284d8adcd53234583cec976
  - AspisLib_Recorded 9ac75bc9413f0cdb5445e77da4ed49ec628942c04ce758f4a729e064b5293f6f
  - AspisLib_SourceInputs 33467d8e490519e2a1829a10babe65b63db378b993359dd0f2e98aeb2c16a90f
  - AspisLib_Tag 7866e76d0c5ee802162e99b8aea1f48147b6afed553c9613dc4cffddfe37a8de
- L187 objects: `~/aspis-lead-infra/l187-closure/{objs,base}`, read by reference only.
- Toolchain: Lean 4.32.0 (`~/.elan/toolchains/leanprover--lean4---v4.32.0`), run on the Mac. Every module was
  compiled with `lean -j1 -M7000 -DElab.async=false`, one process at a time (`tools/compile.sh`).
- `LEAN_PATH` order: own object directory, L187 `objs`, L187 `base`, then the lead's `aspis-lib/objs` last.
  The lead's directory also holds a trimmed `BinHonestStartFrames.olean`. With this order that file is never
  loaded: every L187 module, `BinHonestStartFrames` included, resolves to the unchanged L187 object, and only the
  six base modules come from the lead's directory. The "before" objects were compiled with the same order,
  without the lead's directory.

## What changed, per module

Name replacements: `AspisR1.RecordedBinaryExperimentBin.{dec, binaryCollision}` became
`AspisR1.AspisLib.RecordedBinaryExperimentBin.{dec, binaryCollision}`.
`AspisR1.OraclePortAdmission.Guard` became `AspisR1.AspisLib.OraclePortAdmission.Guard`.
`AspisR1.InitialTagDecision.erased_transcript_tag` became
`AspisR1.AspisLib.InitialTagDecision.erased_transcript_tag`.
`AspisR1.DecoderQueryAccounting.{starts_le_queries, AdversaryQueries}` became
`AspisR1.AspisLib.DecoderQueryAccounting.{...}`. `AspisR1.BinHonestQueryBudget.raw` became
`AspisHonestBudgetBase.raw`. Comments that name the original constants were left as they were. The script that
made the edits, with a count assertion for each, is `tools/repoint.py`.

| Module | Change |
|---|---|
| AspisRows40Starts | `import BinHonestQueryBudget` replaced by `import AspisHonestBudgetBase` and `import AspisLib_Recorded`; the opens of `RecordedBinaryExperimentBin` and `BinHonestQueryBudget` now open the copies; `unfold ...dec` at one site |
| AspisRows40FinalStarts | open `BinHonestQueryBudget` replaced by open `AspisHonestBudgetBase` (raw) |
| AspisRowStarts40 | the same two opens re-pointed (raw) |
| AspisCharge40 | one `dec` site |
| AspisRec40ChargePrefix | `import AspisLib_QueryAccounting`; one `starts_le_queries` site |
| AspisChargedWeight40 | open re-pointed; one `starts_le_queries` site |
| AspisRec40CallBudget | `import AspisLib_QueryAccounting`; one `AdversaryQueries` site |
| AspisOneTxDecision | `import AspisLib_Guard`; two `Guard` sites (in `dV_aspis` and `accepted_detailsS`); the `SourceInputs` open is unchanged |
| AspisOneTxChecks | three `Guard` sites; the `SourceInputs` open is unchanged |
| AspisRec40CleanTag | `import AspisLib_Tag`; one `Guard` site and one `erased_transcript_tag` site |
| AspisRec40CleanStatement | two `binaryCollision` sites |
| AspisRec40Clean | four `binaryCollision` sites |
| AspisOneTxCheckedAcceptance | three `binaryCollision` sites |
| AspisFailureBound | `import RecordedBinaryExperimentBin` replaced by `import AspisLib_Recorded`; six `binaryCollision` sites |
| AspisRec40CleanRun | bridging step (below) |
| AspisRowStarts | split (below); `import BinHonestQueryBudget` replaced by `import BinHonestStartFrames`; the opens of `RecordedBinaryExperimentBin` and `BinHonestQueryBudget` removed (the part kept uses neither) |
| AspisRowStarts33 (new) | the 33-row part of the old `AspisRowStarts`, text unchanged |
| AspisChargedWeight | `import AspisRowStarts` replaced by `import AspisRowStarts33` |

Total: 40 edited lines. 39 are in the 14 re-pointed modules (6 import lines, 6 open lines, 27 constant sites)
and 1 is the import line of `AspisChargedWeight`. The split and the bridging step come on top of these. `AspisChargedHitMass` and `AspisChargedHitMassCheck` were not edited. They
reach `AspisRowStarts33` through `AspisChargedWeight`.

**Bridging step (one).** In `AspisRec40CleanRun.decodes_r1rows`, `hdec` is the output of
`Frozen2StartChargeCompletion.decodes`, a kind (c) lemma stated about the original `dec`. `rw [hdec]` no longer
matches the goal, which is now stated with the copy. The rewrite now reads
`rw [show AspisR1.AspisLib.RecordedBinaryExperimentBin.dec _ _ = _ from hdec]`. Both are abbreviations of the
same term, so the `show` holds by unfolding. No statement changed.

**Split of AspisRowStarts.** The split followed what the compile and the 40-row chain use. `AspisRowStarts40`
uses `verifierCharge` (in `verifierCharge40_eq`), and `AspisNumeric` uses `verifierCharge_eq`. So `verifierCharge`,
`verifierCharge_eq` and the private `sum_indicator26` stay in `AspisRowStarts`, together with the caps,
`capMax`, `classCap` facts, `wt` and its lemmas, `wt_absorb`, `wt_init` and `rowCharge`. The brief had listed
`verifierCharge` and `verifierCharge_eq` under (ii). Neither uses `dec` or `raw`. `AspisRowStarts33` holds
`sampler_weight`, `row_weight`, `rows_weight` and `verifier_weight`, with the private helpers `ite_le` and
`weight_le_zero_of_count` that only they use. It is in the same namespace, and its text is unchanged. It keeps
`import BinHonestQueryBudget` and the original `dec`, `raw` and `query_tail_zero`. The `#print axioms` lines moved
with their theorems. Script: `tools/split.py`.

## What could not be re-pointed: SourceInputs

`AspisLib_SourceInputs` declares `SourceInputs` as a new `structure`. It is not an abbreviation of
`AspisR1.R1FinalSoundness.SourceInputs`, so the two are different types. `AspisOneTxDecision.arithmeticS` applies
`verifyS` to the output of `OraclePortStoredDecisionDraftC4.input`. That is a kind (c) definition, and it returns
`Option RecordedBinaryExperimentBin.SourceInputs`, which is the original structure. With `verifyS` re-pointed,
the compile failed at lines 171 and 188 ("Application type mismatch ... has type
RecordedBinaryExperimentBin.SourceInputs but is expected to have type SourceInputs";
`logs/AspisOneTxDecision.fail1.out`). The fix would need a conversion between the two structures, or a change
to what `input` returns. Either is more than a bridging step. The `SourceInputs` opens in `AspisOneTxDecision`
and `AspisOneTxChecks` were therefore left on the original. Every `SourceInputs` use in the chain stays on
`R1FinalSoundness`/`RecordedBinaryExperimentBin`.

## Compile

`compile-after.tsv` has, per module: status (changed, downstream of a change, or unchanged upstream), whether the
module is in the model closure, the source sha256, exit, wall time and peak RSS (`/usr/bin/time -l`). All 77
modules exit 0. That is the 73 of the model closure (18 changed or new, counting the 33-row side, and 23
downstream) plus `AspisRowStarts33`, `AspisChargedWeight`, `AspisChargedHitMass` and `AspisChargedHitMassCheck`.
The model closure took 181.6 s summed. The largest peak RSS was 3,691,806,720 B (`AspisRec40FinalWords`). No
module came near 7 GB or ten minutes.

The objects come from three passes over the same final sources. Pass 1 stopped at `AspisOneTxDecision`
(SourceInputs). Pass 2 stopped at `AspisRec40CleanRun` (before the bridging step). Pass 3 ran from
`AspisRec40CleanRun` to the end. Each row records its pass. The merge script checked that every row's sha256
equals the committed source, so no object was compiled from a different text. The two failed attempts are in
`compile-after-failures.tsv`. No output contains `sorry`. There are 21 linter warnings, the same count as before.

Before: the unchanged 76 modules were compiled into a separate object directory (`compile-before.tsv`). All exit 0,
207.1 s summed, largest peak RSS 3,692,298,240 B. No copy of the replay-c1 objects was on the Mac.

## Checks

a. **Axioms: pass.** `checks/statements-after.out` shows that `failure_bound40P_model` and
   `failure_le_per_query_model` each depend on `[propext, Classical.choice, Quot.sound]`.

b. **Statement identity: pass.** `checks/X5Statements.lean` (with `pp.fullNames true` and width 100000, then
   `pp.all true`) gives byte-identical output from the before and after objects. Both
   `checks/statements-before.out` and `checks/statements-after.out` have sha256
   f474e291bcb458ce09753aacea0fb34a2a4f2eea291bd62a00e44774d9c0c9cf. No replaced constant occurs in either
   statement. The changes are inside definitions the statements name, such as `AspisFailureBound.exp` through
   `dV_aspis`. A side check, `checks/X5CopiesDefeq.lean`, ran in the after environment, where both versions are
   loaded. It shows that each replaced definition (`Guard`, `dec`, `binaryCollision`, `AdversaryQueries`, `raw`)
   equals its original by `rfl`. Exit 0, empty output.

c. **No carrier use: fail (41 lines, all from two causes).** `checks/AspisChainUsesD.lean` is
   `AspisChainUses.lean` with the watch list reduced to the 38 kind (d) modules. Run on the after objects
   (exit 0, peak RSS 3,612,033,024 B), it writes `checks/uses-d-after.tsv`. The 89 kind (d) uses from before are
   down to 41:
   - 40 are `SourceInputs` and its projections. They occur in `AspisOneTxDecision` (`verifyS`,
     `verifyS_accepted`, `arithmeticS`, `arithmeticS.match_1`, `accepted_detailsS`), `AspisOneTxChecks`
     (`ofTypedS`, `accepted_checks_aspis`), `AspisOneTxRun` (`accepted_checks40`, `slots_read40`, `targets40`),
     `AspisOneTxCheckedAcceptance` (`canonical_valid40`) and `AspisRec40CleanTag` (`guard_tag`).
   - 1 is `RecordedBinaryExperimentBin.dec` in `AspisRec40.CleanRun.decodes_r1rows`. It is inherited from the
     statement of the kind (c) lemma `Frozen2StartChargeCompletion.decodes`, so no chain edit can remove it.

   Nothing uses `Guard`, `binaryCollision`, `erased_transcript_tag`, `starts_le_queries` or `AdversaryQueries`
   from a carrier any more, and nothing uses `dec` except the inherited case.

   Direct imports: `chain-direct-imports-after.tsv` lists every direct import of all 77 modules. None is kind (d).
   The only direct kind (d) import before was `AspisFailureBound -> RecordedBinaryExperimentBin`, and it is gone.
   Neither `AspisRowStarts` nor `AspisRows40Starts` imports `BinHonestQueryBudget`. That module is still in the
   closure through kind (c) modules: `R19BudgetSamplerReads`, `BinInitialQueryAccounting`, and the kind (d)
   `R1FinalSoundnessBinPerQuery`.

d. **Kind (d) modules still in the import closure of AspisFailureBoundModel: all 38.**
   `checks/ImportGraph.lean` dumps the loaded import graph (7,130 modules after, 7,124 before), and
   `tools/closure_d.py` analyses it. The kind (d) modules are entered through 11 edges from kind (c) modules:
   - BinDecoderInitialStarts -> RecordedBinaryExperimentBin
   - BinHonestStartFrames -> DecoderQueryAccounting
   - DecoderFiniteStartSupport -> DecoderQueryAccounting
   - OraclePortCompactDraft -> OraclePortChecks
   - OraclePortCompletionDraft -> OraclePortAdmission
   - OraclePortDataChoiceDraft -> OraclePortChecks
   - OraclePortStoredAdmissionC4 -> OraclePortChecks
   - R15WriterModel -> R1FinalSoundnessBinPerQueryR18
   - R16DecisionErasure -> R1FinalSoundnessBinPerQueryR19
   - R9PoolCheckpointCodec -> R9DeployedBinaryExperiment
   - RWireInitialTag -> RecordedBinaryExperimentBin

   The per-module list (each kind (d) module with the entry edges it is reached from) is in
   `checks/closure-d-after.txt`. The before list is in `checks/closure-d-before.txt`. The only difference is the
   removed chain edge `AspisFailureBound -> RecordedBinaryExperimentBin`. The compressed graphs are in
   `checks/import-graph-{before,after}.tsv.xz`.

e. **33-row side: pass.** `AspisRowStarts33`, `AspisChargedWeight`, `AspisChargedHitMass` and
   `AspisChargedHitMassCheck` compile (exit 0). None of them is in the import closure of `AspisFailureBoundModel`
   (`in_closure ... False` in `checks/closure-d-after.txt`).

## For the kind (c) trim

Two items need it:
- `OraclePortStoredDecisionDraftC4.input` (and anything that states facts about it) must produce the carrier-free
  `SourceInputs`. The alternative is for the carrier-free module to keep the original structure under its
  original name, so that the chain needs no change.
- `Frozen2StartChargeCompletion.Decodes`/`decodes` is stated about `RecordedBinaryExperimentBin.dec`.

## Not done

- `SourceInputs` is not re-pointed, so check c is not empty.
- Nothing was run on the build host or under the new toolchain.
- No package-wide replay was run.
