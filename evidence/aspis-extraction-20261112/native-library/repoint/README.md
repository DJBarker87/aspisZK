# X5: re-pointing the Aspis model chain to the carrier-free library

Status: target not yet established. This is a refactor record. Nothing in it is a new proof, and no theorem is
newly established. Round 2 (this text) is a source change only. It was not compiled. The compile and the five
checks are left to a build-host run, described in "For the host compile" below.

## Round 2: original names (current state)

The soundness lead regenerated the carrier-free base modules (research commit 6032f9ef5bd,
`docs/research/100bit-spend-path-20261013/evidence/pin2-replay-20261111/aspis-lib/`, revision 2 in its
`ASPISLIB_RECORD.md`). They now declare the seven names under their original fully qualified names:
- `AspisR1.R1FinalSoundness.SourceInputs` in `AspisLib_SourceInputs`;
- `AspisR1.RecordedBinaryExperimentBin.{SourceInputs, dec, binaryCollision}` in `AspisLib_Recorded`;
- `AspisR1.InitialTagDecision.erased_transcript_tag` in `AspisLib_Tag`;
- `AspisR1.DecoderQueryAccounting.{starts_le_queries, AdversaryQueries}` in `AspisLib_QueryAccounting`;
- `AspisR1.OraclePortAdmission.Guard` in `AspisLib_Guard`.

`AspisHonestBudgetBase.raw` keeps its own namespace. So the chain needs no renamed constant, and the
`SourceInputs` obstruction of round 1 disappears: `OraclePortStoredDecisionDraftC4.input` and the chain's
`verifyS` now name the same structure.

Reverted from round 1 (`tools/revert_names.py`, with an occurrence count asserted for each edit):
- the 27 constant sites, back to the original names;
- the three `open` lines that opened `AspisR1.AspisLib.RecordedBinaryExperimentBin`, back to
  `open RecordedBinaryExperimentBin` (in `AspisRows40Starts`, `AspisRowStarts40`, `AspisChargedWeight40`), and
  the round-1 removal of that open in `AspisRowStarts`;
- the bridging `show` in `AspisRec40CleanRun.decodes_r1rows`, back to `rw [hdec]`;
- the round-1 doc note added to `AspisRowStarts`.

Kept:
- the import changes, so that no chain module imports a kind (d) module directly;
- the `raw` change (`open BinHonestQueryBudget` became `open AspisHonestBudgetBase`, and the import changed with
  it);
- neither `AspisRows40Starts` nor `AspisRowStarts` imports `BinHonestQueryBudget`;
- the `AspisRowStarts` / `AspisRowStarts33` split, unchanged from round 1.

`AspisRowStarts` now imports `AspisHonestBudgetBase` (which imports `BinHonestStartFrames`) and
`AspisLib_Recorded`. The second import is there because the file's original `open RecordedBinaryExperimentBin`
line needs that namespace, and after the change nothing else in its chain imports provides it.

### Differences from the chain before X5

The baseline is the parent of 9143734d3eb (the lean directory last changed at 5bf1b2216ff). The full table is
`diff-vs-before.tsv`, made by `tools/diffclass.py`. It has one row per module, with lines removed and added, the
kind of each changed line, any line outside the allowed kinds, and the sha256 after the change, for all 77
modules. Every changed line is an import line, a `raw` open line, or a declaration moved to `AspisRowStarts33`.
No changed line falls outside these three kinds, in any module.

| Module | Removed / added lines | Kind |
|---|---|---|
| AspisRows40Starts | 2 / 3 | import (`BinHonestQueryBudget` replaced by `AspisHonestBudgetBase` and `AspisLib_Recorded`), raw open |
| AspisRows40FinalStarts | 1 / 1 | raw open |
| AspisRowStarts40 | 1 / 1 | raw open |
| AspisRec40ChargePrefix | 0 / 1 | import `AspisLib_QueryAccounting` |
| AspisRec40CallBudget | 0 / 1 | import `AspisLib_QueryAccounting` |
| AspisOneTxDecision | 0 / 1 | import `AspisLib_Guard` |
| AspisRec40CleanTag | 0 / 1 | import `AspisLib_Tag` |
| AspisFailureBound | 1 / 1 | import (`RecordedBinaryExperimentBin` replaced by `AspisLib_Recorded`) |
| AspisRowStarts | 117 / 3 | import (`BinHonestQueryBudget` replaced by `AspisHonestBudgetBase` and `AspisLib_Recorded`), raw open, 112 declaration lines plus 3 `#print axioms` lines moved to `AspisRowStarts33` |
| AspisRowStarts33 (new) | 148 lines | the moved lines, verbatim (checked as one contiguous block of 112 lines), under the original header with `import AspisRowStarts`, `import BinHonestQueryBudget` and a doc note |
| AspisChargedWeight (33-row side) | 1 / 1 | import (`AspisRowStarts` replaced by `AspisRowStarts33`) |

The other 66 modules are byte-identical to the baseline. The text checks also hold:
- no chain source contains `AspisLib.`;
- no chain module imports a kind (d) module (`chain-direct-imports.tsv`);
- the import closure of `AspisFailureBoundModel` within the chain is the same 73 modules as before
  (`host-order-model-73.txt`), and contains none of the four 33-row modules.

What moved: `sampler_weight`, `row_weight`, `rows_weight`, `verifier_weight`, and the private `ite_le` and
`weight_le_zero_of_count`. `verifierCharge`, `verifierCharge_eq` and `sum_indicator26` stay in `AspisRowStarts`,
because `AspisRowStarts40.verifierCharge40_eq` and `AspisNumeric` use them. Round 1's compile showed this.

### What stands from round 1

- `compile-before.tsv`: the unchanged 76 modules compiled on the Mac under Lean 4.32.0 against the L187 objects.
  All exit 0, 207.1 s summed, largest peak RSS 3,692,298,240 B. All hashes equal the replay-c1 manifest.
- `checks/statements-before.out` (sha256 f474e291bcb458ce09753aacea0fb34a2a4f2eea291bd62a00e44774d9c0c9cf) is the
  reference for the statement-identity check. It holds both statements with `pp.fullNames`, then with `pp.all`,
  and the axioms lines.
- `checks/closure-d-before.txt` and `checks/import-graph-before.tsv.xz`: the loaded import graph before X5.
- Round 1's after-results are in `round1/`. They come from the renamed-constant version, so the after objects,
  check outputs and failure logs there describe a source that no longer exists. What carries over from them:
  - the split boundary, which is unchanged;
  - the fact that, apart from `SourceInputs`, every replaced definition was `rfl`-equal to its original;
  - the list of kind (c) -> kind (d) entry edges (`round1/checks/closure-d-after.txt`).

## For the host compile

**Why not on the Mac.** A base module and its carrier cannot be in one environment (the soundness lead's test:
"environment already contains AspisR1.R1FinalSoundness.SourceInputs._sizeOf_1"). Under the L187 objects, the
earlier-proof modules still import the carriers. The run needs an object set in which the base modules come first,
then the kind (c) modules with their carrier imports replaced (`trim_imports.py --map`, `IMPORT_MAP.txt`), and
those trimmed objects shadow the L187 objects on `LEAN_PATH`.

**Order.**
- `host-order-77.txt`: all 77 modules in dependency order.
- `host-order-model-73.txt`: the 73 in the closure of `AspisFailureBoundModel`.
- `AspisRowStarts33`, `AspisChargedWeight`, `AspisChargedHitMass` and `AspisChargedHitMassCheck` come last and
  are a side check.

**Base modules needed.** `needs-base.tsv` gives, for each chain module that uses one of the seven names or `raw`,
the base module that declares it and the chain import path that reaches it. Every path runs through chain imports
only, and the direct base imports are:
- `AspisRows40Starts`: `AspisHonestBudgetBase`, `AspisLib_Recorded`;
- `AspisRowStarts`: `AspisHonestBudgetBase`, `AspisLib_Recorded`;
- `AspisRec40ChargePrefix`: `AspisLib_QueryAccounting`;
- `AspisRec40CallBudget`: `AspisLib_QueryAccounting`;
- `AspisOneTxDecision`: `AspisLib_Guard`, which imports `AspisLib_Recorded`, which imports `AspisLib_SourceInputs`;
- `AspisRec40CleanTag`: `AspisLib_Tag`;
- `AspisFailureBound`: `AspisLib_Recorded`.

`AspisRowStarts33` imports `BinHonestQueryBudget`, which is kind (c) and trimmed on the host.

Two kind (c) lemmas that the chain uses are stated about these names. `OraclePortStoredDecisionDraftC4.input`
returns `SourceInputs`, and `Frozen2StartChargeCompletion.decodes` is stated about `dec`. They must be compiled
against the base modules, which happens in the trim.

**Compile.** One module at a time, `lean -j1 -M7000 -DElab.async=false`, each in a capped scope. Record per
module: source sha256 (it must equal the `sha256_after` column of `diff-vs-before.tsv`), exit, wall and peak RSS.
`tools/compile.sh` does this, but it is written for the Mac:
- it uses macOS `/usr/bin/time -l`, which becomes `/usr/bin/time -v` on Linux;
- its `LEAN` and `L187` paths must be set to the host's;
- its `LEAN_PATH` order is own objects, L187 `objs`, L187 `base`, then extras. On the host the trimmed
  kind (c) objects and the base objects must come before L187 `objs`.

**Checks and expected outputs.**
- a. In `checks/X5Statements.lean`, both `#print axioms` lines must read exactly:
  `'AspisFailureBoundModel.failure_bound40P_model' depends on axioms: [propext, Classical.choice, Quot.sound]`
  and
  `'AspisFailureBoundModel.failure_le_per_query_model' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- b. The output of `checks/X5Statements.lean` must be byte-identical to `checks/statements-before.out` (125 lines,
  sha256 f474e291bcb458ce09753aacea0fb34a2a4f2eea291bd62a00e44774d9c0c9cf). No constant is renamed in round 2, so
  no name substitution is needed before comparing.
- c. Run `checks/AspisChainUsesD.lean` (watch list: the 38 kind (d) modules) on the after objects. It must
  produce an empty `uses_d_after.tsv`; the `lines` count in its info message must be 0. A useful addition is the
  six base modules on the watch list with tag `base`. That would show the seven names now resolve to
  `AspisLib_*`; in round 1's terms, at most the 89 former kind (d) uses, now attributed to base modules. Direct
  imports: `chain-direct-imports.tsv` already shows, from the source text, that no chain module imports a
  kind (d) module.
- d. Run `checks/ImportGraph.lean` and then `tools/closure_d.py <graph> <kind-d list> <chain file list>`. List
  each kind (d) module still in the closure and its entry edge. After a complete trim the expected list is
  empty. Before the trim, round 1 found 11 entry edges from kind (c) modules: BinDecoderInitialStarts,
  BinHonestStartFrames, DecoderFiniteStartSupport, OraclePortCompactDraft, OraclePortCompletionDraft,
  OraclePortDataChoiceDraft, OraclePortStoredAdmissionC4, R15WriterModel, R16DecisionErasure, R9PoolCheckpointCodec
  and RWireInitialTag.
- e. The four 33-row modules compile, and `closure_d.py` prints `in_closure ... False` for each.

**Reusable scripts.**
- `tools/order.py`: dependency order of chain modules.
- `tools/compile.sh`: needs the adaptations above.
- `tools/closure_d.py`: kind (d) modules in the closure and their entry edges.
- `tools/diffclass.py`: the text-difference check.
- `checks/X5Statements.lean`, `checks/AspisChainUsesD.lean`, `checks/ImportGraph.lean`: the Lean checks. Each is
  run from its own directory and writes its output there.

The round-1 scripts `tools/repoint.py` and `tools/split.py` are kept as the record of how the text was made.

## Not done

- Round 2 was not compiled. None of the five checks was run on round 2.
- What is verified for round 2 is text only:
  - the difference table and the moved block, checked by git and difflib;
  - the absence of `AspisLib.` names;
  - the direct imports;
  - the chain import order.
