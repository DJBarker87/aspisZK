# The recorded/charged experiment for the Aspis 40-row protocol (plan item 13)

Status (updated, section 5): the hit-mass equality with the terminal decision as a parameter compiles. The measurement is done (section 1). The charged experiment and its
start count for 40 rows compile (section 2). The clean event and the
full-to-charged hit-mass equality do not copy as they stand, because R1 states
them on its full experiment, which is built with R1's two-transaction decision
(section 3). No event was weakened, no assumption added, and the Rust is not
touched. No security figure is quoted.

## 1. Measurement

Method: Lean itself was used (`AspisRec40Measure.lean`, attempt PSD-24,
exit 0, 4.86 s, 4,230,932 KB). The file imports `Frozen2StartChargeProbability`,
`DecoderQueryAccounting` and `RawFullPublicSelection`. For each group of root
declarations it walks the constant-dependency graph (types and proof terms)
and records the module of every constant reached. It expands only through
modules that depend on a replaced definition or are two-transaction modules
(the 555 rows of `aspis-instance-module-classes.tsv` with
`depends_on_changed_defs = yes` or class iii). A constant in any other module
is a leaf: that module is reused unchanged. A module counts as
whole-protocol if its code (comments stripped) names
`LiteralByteProtocol.protocol/rows`, `LiteralClassifier.bad/budget`,
`UnifiedDecoder.decode`, `RawUnifiedDecoder.decode`,
`RecordedBinaryExperimentBin.dec` or `dec`, or a literal 33/34. That test
over-approximates.

| Root group | Roots | Changed-dependent modules reached | of which whole-protocol (test) | two-transaction (iii) |
|---|---|---:|---:|---:|
| charged | `Frozen2StartChargePrefix.{charged, charged_eval, prover_eval, base}` | 17 | 13 | 0 |
| starts | `Frozen2StartChargePrefix.starts`, `DecoderQueryAccounting.starts_le_queries`, `RecordedBinaryExperimentBin.dec` | 50 (with charged) | 28 | 0 |
| clean | `Frozen2StartChargeClean.{clean, bad, prefixHit}` | 251 | — | 14 |
| hit mass | `Frozen2StartChargeProbability.{hit_mass, restricted_union_bound}` | 118 | — | 10 |
| clean ∪ hit mass ∪ charged ∪ starts | | 266 | 111 | 14 |
| honest-run selection | `RawFullPublicSelection.bounded_at_first_cell` | 54 | 19 | 0 |

### 1.1 Charged experiment and start count: the minimal set is 2 copies

Of the 50 changed-dependent modules on this path, only two need Aspis
content. Every other one is reused unchanged:

- **R1's byte-decoder chain, reused as a component of `decFinal`.**
  `decFinal = decAspis fin` contains R1's `RecordedBinaryExperimentBin.dec`
  unchanged (ROWS-33-39.md §3). So these are reused as R1 objects:
  `RecordedBinaryExperimentBin`, `RawAdaptiveLiteralDecoder`,
  `RawLiteralDecoderDensity`, `RawUnifiedDecoder`, `UnifiedDecoderCanonical`,
  `BackgroundCanonicalLabels`, `RawFullPublicSelection`,
  `RawPublicSelectionLift`, `FullPublicSelection`, `R1UnifiedDecoder` and its
  component decoders, `R1UnifiedLabels`, and the selection and init-parser
  modules (`EarlyPublicSelection`, `SemanticPublicSelection`,
  `RawPublicOpeningWalk`, `RawLatePublicSelector`, `RawPublicInit*`,
  `InitialPublicWalk`).
- **Already replaced by AspisRows40 files.** R1's 33-row count
  `BinHonestQueryBudget.verifier_starts` and `BinHonestStartFrames` are
  replaced by `AspisRows40.FinalStarts.verifier_starts` (≤ 41). R1's
  `LiteralByteProtocol.protocol` is replaced by `AspisRows40.Protocol.protocol`
  (r := 40). R1's `LiteralTranscript.valid` is replaced by `valid40`.
- **Reused unchanged through the delegation lemmas.**
  - `BinCompiledRunWordStability.wordsFromRun D` reads the first cells of rows
    0, 2 and 30 of `LiteralByteProtocol.protocol D`'s chains. Those chains are
    the 40-row protocol's chains for every row (`Protocol.chain_eq`).
  - `R1UnifiedSampler`, `R1LiteralByteSampler` and `R1LiteralTranscript`:
    the sampler and the message carrier are R1's.
  - `R16CanonReduction.proof` retags only rows 0, 2 and 30, so it fixes the
    payload messages of rows 33–39.
- **Generic in the protocol, reused (instantiated, not copied).**
  `DecoderQueryAccounting.starts_le_queries` (any decoder),
  `RawCutProverCompiler.{experiment, experiment_eval, Prover, RunView}`,
  `OraclePortStoredExperimentC4.Prover`, `OraclePortStoredAdmissionC4.canon`,
  `OraclePortStoredProjectionC4.project`,
  `RawRecordedOracleExtractionMassBin.Experiment`,
  `CanonicalCutEnrichedTranscript`, `BinCanonicalCutWords`,
  `LiteralTableWordChoice{,Bin}`, `LiteralDecoderEnrichment` (identity on
  rows ≥ 33, `Literal.enrich_final`), `LiteralLegacyRun`,
  `RawCutTranscriptRun`, `RawCutWordsFromView` (definitions), and the
  `R1Joint*`/`R1Unified*Decoder` modules as R1 components.
- **Copy with changed instance (2).**
  `RawCutProverCompiler.{compiled, eval_compiled}` names R1's 33-row
  `verifier`, and becomes `AspisRec40Compiler`.
  `Frozen2StartChargePrefix.{base, charged, charged_eval, prover_eval, starts}`
  becomes `AspisRec40ChargePrefix`; `starts` changes `Q + 34` to `Q + 41`.

So against the plan's estimate of about 117 modules in the
RawCut/RawRecorded/Bin/OraclePort-C4..C6/start-charge families, the charged
experiment and its start count need **2 copied modules**.

### 1.2 Clean event and full-to-charged hit mass

`Frozen2StartChargeClean.clean` and `Frozen2StartChargeProbability.hit_mass`
are stated on R1's full experiment:

```
OraclePortFrozen2Consumer.projected D P := bind (annotated D dV (canon P)) …
dV := OraclePortFrozen2.dV_frozen2          -- OraclePortFrozen2Decision.lean:40, class iii
```

`dV_frozen2` is R1's two-transaction terminal decision. It splits the batch
Merkle checks at `batch0` / `afterBatch0`, the TX1/TX2 split. On this path the
measurement reaches 14 two-transaction modules: `OraclePortFrozen2{Decision,
Bounds, Checkpoint, Trace}`, `OraclePortCheckpoint{StateC3, AbiC5, OracleC5,
PreparedC5, ResumeC5, SlicesC5}`, `OraclePortAcceptedContextC6`,
`R16Decision{Checkpoint, QueryModel}` and `R1VerifierCallBudget`. Under the
rules none of them is copied. The Aspis full experiment needs the Aspis
terminal decision (the merged multiproofs and the summed final checks of the
one-transaction verifier). That is new content, in the one-transaction game's
domain (plan item 15, ONE-TRANSACTION-GAME.md §3.4, "the Aspis decision is
modelled on `OraclePortFrozenOrderDecision.dV_frozen`").

The two theorems then split:

- **hit mass** (`hit_mass`, `recovered`, `recovered_eval`,
  `chronological_prefix`, `same_transcript`). This is a statement about any
  full experiment whose trace starts with the charged trace. R1's proof uses
  `OracleDecisionPrereqStarts.annotated`,
  `OracleDecisionFeasibilityCompiler.compiled_experiment_eval` and
  `OraclePortSamplerPrefixDraft.{split_trace, words_prefix, output_pair}`.
  These take the decision as a parameter but name R1's 33-row protocol
  through `OracleDecisionFeasibilityCore.verifier`. They can be copied with
  the decision as a parameter, about 5–7 modules (`OracleDecisionFeasibilityCore`,
  `…Compiler`, `OracleDecisionPrereqStarts`, `OraclePortSamplerPrefixDraft`,
  `OraclePortExperiment`, and the `projected`/`recovered` parts of
  `OraclePortFrozen2Consumer`/`Frozen2StartChargePrefix`). Their instance at
  the Aspis decision then waits for that decision.
- **clean** (`Frozen2StartChargeClean.clean` through
  `OraclePortFrozen2Consumer.fibre_checks`). This uses
  `OraclePortFrozen2C6.checked_acceptance`, i.e. acceptance gives the checks.
  That is the acceptance link (another agent). It is not a copy job until the
  Aspis acceptance-to-checks theorem exists.

The remaining whole-protocol modules reached only from clean/hit mass (83,
listed in the measurement output) are mostly that acceptance chain (`RWire*`,
`OraclePort*C6`, `R1LiteralAcceptanceTerminal`, `R1Unified{Recovery, Verifier,
Protocol, TraceReads, …}`), plus the classifier envelope
(`R1LiteralClassifier`, `LiteralBudgetEnvelope`, `R1PerAttemptEnvelope`,
`RawAdaptiveClassifierStartBound`), which belongs to items 8 and 14.

### 1.3 "Exactly one start per new row in an honest run"

R1's honest-run selection (`RawFullPublicSelection.bounded_at_first_cell`)
reaches 54 changed-dependent modules, 19 whole-protocol by the test. They are
the 33-row run model: `R1Unified{Protocol, Verifier, Recovery,
PrefixedReads, TraceReads}`, `LiteralLegacy{Run, VerifierTrace}`,
`FullPublic{Early, Opening, RhoCasePublicAPI, Total}Case`,
`RawPublic{Opening, Rho}Recovery`, `R1LiteralByteProtocol`,
`R1LiteralProtocol`, `R1LiteralTranscript`, `R1UnifiedLabels`,
`R1UnifiedSampler`, `RawFullPublicSelection`. The 40-row form of
conditions (i)–(iii) of `FinalStarts.row33_one` (ROWS-33-39.md §7.4) needs a
40-row copy of that run model: about 10–12 copies once the labels, sampler and
protocol already delegate. This is not started; see section 4.

## 2. Copies that compile

R1's statement, with protocol, decoder and row bound replaced, and nothing else:

| Aspis | R1 | Change |
|---|---|---|
| `AspisRec40.Compiler.compiled D d build P` | `RawCutProverCompiler.compiled` | verifier `RawCutProverCompiler.verifier D d` → `AspisRows40.Starts.verifier D d` |
| `AspisRec40.Compiler.eval_compiled` | `RawCutProverCompiler.eval_compiled` | same; same proof |
| `AspisRec40.ChargePrefix.prover` | `Frozen2StartChargePrefix.prover` | none (generic) |
| `AspisRec40.ChargePrefix.base` | `Frozen2StartChargePrefix.base` | 40-row verifier |
| `AspisRec40.ChargePrefix.charged` | `Frozen2StartChargePrefix.charged` | 40-row compiler; `wordsFromRun D` unchanged |
| `AspisRec40.ChargePrefix.charged_eval` | `Frozen2StartChargePrefix.charged_eval` | same proof with the 40-row compiler |
| `AspisRec40.ChargePrefix.prover_eval` | `Frozen2StartChargePrefix.prover_eval` | none; same proof |
| `AspisRec40.ChargePrefix.starts : decoderFirstReads decFinal emptyTable (eval H (charged D P)).1 ≤ Q+41` | `Frozen2StartChargePrefix.starts : … RecordedBinaryExperimentBin.dec … ≤ Q+34` | decoder `dec` → `decFinal`; `34` → `41`, from `FinalStarts.verifier_starts`; hypothesis `hq` unchanged |

| Attempt | Module | Source sha256 | Exit | Wall | Peak RSS (time) | cgroup peak | Axioms |
|---|---|---|---|---|---|---|---|
| PSD-24 | AspisRec40Measure (measurement only) | 8bead73c…201a6ad42 | 0 | 4.86 s | 4,230,932 KB | 442,966,016 B | none printed |
| PSD-25 | AspisRec40Compiler | 11c35103…9bee7536 | 0 | 2.57 s | 4,192,308 KB | 432,201,728 B | 1× [propext, Classical.choice, Quot.sound] |
| PSD-26 | AspisRec40ChargePrefix | 862c6c830439e2aed5535fca9a647af435095573ffeca78355a1587bfc9a9750 | 0 | 3.71 s | 4,208,628 KB | 430,391,296 B | 3× [propext, Classical.choice, Quot.sound] |

No `sorry`, no new axioms.

## 3. Where the copying stops, and why

The next modules in dependency order are R1's full experiment
(`OraclePortFrozen2Consumer.projected`) and the theorems stated on it (`clean`,
`hit_mass`). They take R1's two-transaction decision `dV_frozen2`, which is
class iii and not to be copied. Substituting anything for it would mean
inventing the Aspis decision, which belongs to the one-transaction game and
the acceptance link. So this stops at the boundary rather than making that
choice. Two ways on, for the lead:

1. Copy the hit-mass chain with the full experiment parametric in a
   decision `d : OraclePortStoredExperimentC4.Decision` (about 5–7 copies).
   The result would be "for every decision d, the full-experiment prefix-hit
   mass equals the charged hit mass". It is instantiated when the Aspis
   decision exists.
2. Wait for the Aspis decision and acceptance link, then copy the clean
   event as well.

## 4. Files

- `lean/AspisRec40Measure.lean`: measurement script, no theorems. The host
  copy reads `lean-src/measure-expand.txt`, which is the 555-module list
  derived from the TSV. Output: `lean-src/measure-*.tsv` on the build host.
- `lean/AspisRec40Compiler.lean`, `lean/AspisRec40ChargePrefix.lean`.

## 5. The hit-mass chain with the terminal decision as a parameter (lead's decision, way 1)

### 5.1 The statement, and the hypotheses on the decision

```lean
-- AspisRec40.HitMass.hit_mass
theorem hit_mass (cls : Classifier) (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) :
    lazyMean (projected D d P) emptyTable (fun run => indicator (prefixHit cls D P run)) =
      lazyMean (AspisRec40.ChargePrefix.charged D P) emptyTable (fun run => indicator
        (hitsChain3 AspisRows40.FinalStarts.decFinal cls emptyTable run.1))
```

Here:
- `Decision` is `OraclePortStoredExperimentC4.Decision`, i.e. `Bytes →
  ErasedPrefix → ErasedMessage → Program Bytes State Bool`, the type of R1's
  `dV_frozen2`. `decision_type` checks it by `rfl`.
- `Prover` is R1's stored-input prover type.
- `Classifier` is the type of R1's `RawAdaptiveClassifierHitDensity.classifier`;
  the Aspis classifier belongs to another agent.
- `projected D d P := bind (annotated D d (canon P)) fun v => .done ((v.1.statement, v.1.proof), v.2)`
  is R1's `OraclePortFrozen2Consumer.projected` with `dV_frozen2` replaced by `d`
  and the 40-row verifier in place of R1's.
- `prefixHit cls D P run := hitsChain3 decFinal cls emptyTable (recovered D P run).1`.

R1 (`Frozen2StartChargeProbability.hit_mass`):
`lazyMean (projected D P) emptyTable (fun run => indicator (prefixHit D P run)) =
lazyMean (charged D P) emptyTable (fun run => indicator (hitsChain3
RecordedBinaryExperimentBin.dec RawAdaptiveClassifierHitDensity.classifier emptyTable run.1))`.

The changes, and only these:
- R1's decision `dV_frozen2` becomes the parameter `d`, of the same type.
- R1's classifier becomes the parameter `cls`, of the same type.
- R1's `dec` becomes `decFinal`.
- R1's 33-row protocol becomes the 40-row protocol, through the copied verifier,
  experiment and charged experiment.

**Hypotheses on `d`: none.** The proof uses only that the full experiment's
trace starts with the charged trace (`chronological_prefix`). That holds for
every decision, because the decision runs after the 40 sampler rows
(`Decision.split_trace`).

Properties of `dV_frozen2` that R1 uses elsewhere on the bound path, though not
on this one. The one-transaction game agent's decision will need them for
neighbouring theorems:
- `OraclePortExperiment.Budget dO`: at most 1,046 oracle calls per decision
  call, for every input. R1 uses it for the issued-call count
  (`verifier_budget`, ≤ 1,161) and so for the collision envelope `Q + 1161`.
- `OraclePortAdmission.admit (dV s) = dV s` (`OraclePortFrozen2Consumer.admitted_dV`),
  used by the clean event.
- `OraclePortFrozen2C6.checked_acceptance` (acceptance gives the checks), used by
  the clean event.

Also `mass_of_recovered`: for any observable `f`,
`lazyMean (projected D d P) emptyTable (fun run => f (recovered D P run)) =
lazyMean (charged D P) emptyTable f`.

R1's statement as the instance `d := dV_frozen2` is not checked. The copy is
for the 40-row protocol, so instantiating it at `dV_frozen2` would give a
40-row statement, not R1's 33-row one, and it would mean importing
`OraclePortFrozen2Decision` (class iii), which the rules forbid. R1's
statement is R1's own theorem.

### 5.2 Modules

| Aspis | R1 copied | Change |
|---|---|---|
| `AspisRec40.Decision.{verifierFrom, verifier, original}` | `OracleDecisionFeasibilityCore.{verifierFrom, verifier, original}` | 33 → 40 (rows 0–39 sampled; the decision reads prefix 40 and message 40); `Decision` and `onBytes` reused |
| `AspisRec40.Decision.{from_eval, verifier_eval}` | `OracleDecisionFeasibilityBudget.{from_eval, verifier_eval}` | 33 → 40, 40-row protocol; same proof |
| `AspisRec40.Decision.{verifierFrom_eq, verifier_eq, compiled, eval_compiled, compiled_experiment_eval}` | `OracleDecisionFeasibilityCompiler.{…}` | 33 → 40; same proofs (`byte_sampler_eq` and `prefix_ext` are generic in the row) |
| `AspisRec40.Decision.annotated`, `recorded` | `OracleDecisionPrereqStarts.annotated`, `OraclePortExperiment.recorded` | 40-row verifier |
| `AspisRec40.Decision.{base, terminal, split_trace}` | `OraclePortSamplerPrefixDraft.{base, terminal, split_trace}` | 40-row verifier; `FS2.verifier_eval` at `r = 40` |
| `AspisRec40.HitMass.{verifier, original, compiled, recorded, original_eval, compiled_eval}` | `OraclePortStoredExperimentC4.{…}` | 40-row decision verifier |
| `AspisRec40.HitMass.annotated` | `OraclePortStoredAdmissionC4.annotated` | as above |
| `AspisRec40.HitMass.projected` | `OraclePortFrozen2Consumer.projected` | `dV_frozen2` → parameter `d` |
| `AspisRec40.HitMass.{chronological_prefix, recovered, recovered_eval}` | `Frozen2StartChargePrefix.{…}` | see below |
| `AspisRec40.HitMass.{prefixHit, hit_mass}` | `Frozen2StartChargeClean.prefixHit`, `Frozen2StartChargeProbability.hit_mass` | `dec` → `decFinal`; classifier → `cls` |

Not a mechanical copy: `chronological_prefix`. R1 proves it through
`same_transcript`'s ingredients: `annotated_selected`, `fibre_prover` and
`OraclePortStoredReductionC7`, which is a C7 module importing
`OraclePortStoredAcceptanceC6`. Here it is proved directly from the
evaluations, with two helper lemmas stated next to it in the file:
- `projected_trace`: the full trace is the first run's trace followed by a tail.
- `original_canon_trace`: the first run's trace is the 40-row decision
  verifier's trace on R1's projected prover.

`split_trace` and `charged_eval` finish it. The statement is R1's with the
replacements above. The proof route is shorter and goes through no C6 or C7
module.

### 5.3 Two-transaction modules: imported transitively, not used

No class (iii) module is copied, and no constant from one is used. A second
measurement (`AspisRec40Measure2.lean`, PSD-32) walks the constant
dependencies of `hit_mass`, `mass_of_recovered`, `ChargePrefix.starts` and
`FinalStarts.verifier_starts`, expanding through every changed-dependent,
two-transaction and Aspis module. It reaches 246 modules and 1,097 constants,
and **0 class (iii) modules**. No `OraclePortFrozen2*` module is reached.

The import closure, however, does contain 13 modules that the TSV
classifies iii. They come in through R1 modules this work imports unchanged:
- `RecordedBinaryExperimentBin`, i.e. R1's byte decoder `dec`, which `decAspis`
  contains, through `R1FinalSoundness`.
- `R16CanonReduction` (R1's message canonicalisation, used by `canon`).
- `OraclePortStoredAdmissionC4`.

The 13 are: `DecoderInstanceBoundary`, `HchecksPublicComposition`,
`QvStage{1,2}Count`, `R16Decision{Checkpoint, QueryModel}`,
`R19BudgetOriginalReads`, `R1FinalSoundnessBinPerQuery{,R18}`,
`R1FinalSoundnessNumeric`, `R1VerifierCallBudget`, `SharedBinaryRecordGrammar`
and `WireBindingRecordCodec`.

This was already true of the earlier committed files (`AspisRows40Starts`
imports `BinHonestQueryBudget`, whose closure contains
`RecordedBinaryExperimentBin`). The new modules in this step add no iii
import: `OracleDecisionFeasibilityCore` has none in its closure, and neither
do `OracleProgramLawExt` and `OracleProgramReplay`. Removing the import, not
just the use, would need a split of R1's module graph, which this work does
not do.

### 5.4 Validation

| Attempt | Module | Source sha256 | Exit | Wall | Peak RSS (time) | cgroup peak | Axioms |
|---|---|---|---|---|---|---|---|
| PSD-27 | AspisRec40Decision | c5f31e1eb34b970002963e133ce769bb9556bb3499e6923da488b6c5fce51d32 | 0 | 11.04 s | 4,238,408 KB | 471,560,192 B | 7× [propext, Classical.choice, Quot.sound] |
| PSD-31 | AspisRec40HitMass | 8d4e0ec6…270c43563f | 0 | 2.64 s | 4,211,532 KB | 435,265,536 B | 9× [propext, Classical.choice, Quot.sound] |
| PSD-32 | AspisRec40Measure2 (measurement only) | 8db994db…31328dc2 | 0 | 2.57 s | 4,227,160 KB | 444,956,672 B | none (no theorems) |

Earlier attempts on HitMass, all exit 1:
- PSD-28: an existential witness left to unification, and a missing `open` for `Table`.
- PSD-29: `rfl` against a goal with different append associativity.
- PSD-30: a superfluous `rfl` after `rw` closed the goal.

No `sorry`, no new axioms, no option raised. Not started, as instructed: the
clean event, the restricted union bound and the weighted composition (item
14), and the honest-run copies.

### 5.5 Follow-up to the review of 80e6a852d13 (2026-11-11)

The soundness lead's reviewer read the source of the 40 files at 80e6a852d13.
Its verdict: every group it checked follows R1's route, and its caveats
concern provenance and measurement, not the mathematics. It gave no verdict
on the one-transaction acceptance files, which are outside the closure of the
composed bound. It also restated an open point already recorded here:
`AspisChecks` is a hypothesis of the acceptance link, and that an accepted run
of the full experiment supplies it is not yet proved.

Four points needed action.

**1. The constant walk was not rooted at the composed bound.** The walks of
5.3 (PSD-32) and 6.4 (PSD-34) start from `hit_mass`, `starts` and
`verifier_starts`. `AspisHeadlineMeasure.lean` starts from
`restricted_union_bound_weighted40` itself, and from `decFinal_le_charge40`
and `charged_weight40`. It uses no expansion list: it expands every constant
whose module is outside the libraries (Mathlib, Lean core, Std, Batteries,
Aesop, Qq, ProofWidgets, Plausible, ImportGraph, LeanSearchClient), and it
reads proof terms as well as statements. Result (LDM-02):

| Root | Project modules reached | Project constants | Class iii modules reached |
|---|---|---|---|
| `restricted_union_bound_weighted40` | 437 | 4,319 | 0 |
| `decFinal_le_charge40` | 386 | 3,846 | 0 |
| `charged_weight40` | 219 | 1,467 | 0 |

The import closure of the same file has 6,977 modules, 1,541 of them outside
the libraries, and contains the same 13 class iii modules that 5.3 lists. So
the 13 are imported and none of their constants is used by the composed
bound, in its statement or in its proof. The reviewer counted 1,346 modules
in the closure by a different rule; the two counts are not reconciled here,
and the 13 names agree. The module list is in `headline-measure.tsv`
(1,479 lines, sha256 f799261777cf5d38cac3da9356ad2691b6fcea891a04336793afbdd71e887f1d).

The same run checks the one declaration in the Aspis files that raises an
option, `AspisFuture.StageD.perKind_margin` (`exponentiation.threshold 600`,
`StageDSumcheck.lean:710`). It is in none of the three closures.

**2. Five source hashes were mistyped in the notes.** The first eight
characters were right and the abbreviated tail was wrong by one character
(by a transposition for `AspisRows40Starts`). The rows now carry the full
hash, recomputed from the files at 80e6a852d13, which equal the files on the
host:

| Module | Attempt | Note | sha256 |
|---|---|---|---|
| AspisChargedWeight40 | PSA-e-12 | PER-STEP-ACCOUNTING.md, ASPIS-INSTANCE-PLAN.md | 934045c899af9bcf4d369fd90aa94820b2ed208ba333aa514443bf7751f1e404 |
| AspisRec40ChargePrefix | PSD-26 | this note, section 2 | 862c6c830439e2aed5535fca9a647af435095573ffeca78355a1587bfc9a9750 |
| AspisRec40Decision | PSD-27 | this note, 5.4 | c5f31e1eb34b970002963e133ce769bb9556bb3499e6923da488b6c5fce51d32 |
| AspisRowDensityCaps | PSB-06 | ROW-DENSITIES.md | d53896874901f9098e4e6930ceb78e334f12e81e51a104f95d79e90e730313ef |
| AspisRows40Starts | PSD-13 | ROWS-33-39.md | f86ca401206c8b20e60f8f2dbe680b2360a6f3dcdbe853134d415538f9c7865d |

The abbreviations were typed by hand.

Correction, same day: I first wrote here that the receipts do not record the
source hash of an attempt. That was wrong. `fv_lean.sh` prints the sha256 of
the source as the first line of each receipt's `stdout.log` (180 of the 448
receipts have it; the others are older or are not Lean compiles). So every
hash in a note can be checked against what the host compiled.
`tools/check_note_hashes.py` does that for every table row in these notes
that carries an attempt name and a hash. First run: 87 rows, 80 agree, 6
disagree, 1 receipt (PSA-b-02) has no hash line. The 6 were further
mistyped tails of the same kind, in ONE-TRANSACTION-GAME.md (PSE-10, PSE-14,
PSE-23) and PER-STEP-ACCOUNTING.md (PSA-c-01, PSA-c-02, PSA-c-04); the PSE-23
one was also reported by the reviewer of b39cfdd5d57. All 6 now carry the
full hash from the receipt. The five rows above agree with their receipts,
and so does PSB-05. After the fix: 86 agree, 0 disagree.

**3. `AspisFinalSumcheckModel` is not a file name in this repository.** It is
`lean/StageDSumcheck.lean`, copied to the host as
`lean-src/AspisFinalSumcheckModel.lean` so that the module has a plain name.
The two are byte-identical: sha256
5ce44cab5106e797e8bb53dcd3fa2c58355018b7b8aab4e8972607fe896cdd48. The
namespace inside is still `AspisFuture.StageD`. The file is to be renamed in
the repository with the other renames at the next build.

**4. The reviewer did not check that the Rust follows the model's call
order.** That is the point of 6.3: the Rust was changed so that Merkle
authentication comes after rows 33 to 39, as in the model. The agreement is
tested by replay of recorded settlements and is not proved; proving it is
part of the source refinement, which has not started.

| Attempt | Module | Source sha256 | Exit | Wall | Peak RSS (time) | cgroup peak | Axioms |
|---|---|---|---|---|---|---|---|
| LDM-01 | AspisHeadlineMeasure (measurement only), first form | 72ac14ffb7659fab31bec2c4f0e22605185a3027ca1b98b162e36be344d16687 | 0 | 12.48 s | 4,254,044 KB | 461,115,392 B | none (no theorems) |
| LDM-02 | AspisHeadlineMeasure, with the `perKind_margin` check | b8479affda7421b914b5000ed8a2190f810dd2b321ee2cd0fb441609591dcabd | 0 | 6.67 s | 4,257,140 KB | 440,242,176 B | none (no theorems) |

Both runs wrote the same module list. Input `headline-iii.txt` is the 178
class iii rows of `aspis-instance-module-classes.tsv`, sha256
8bc8c737f706ffaef2164dd9e25c01adab0bb341da4853264d5c4f9d79830616.

## 6. Digest-call budget of the 40-row transcript (and the Aspis total)

### 6.1 R1's statements, and the copies

R1 (`OracleDecisionPrereqSampler`, class ii; it does not use
`R1VerifierCallBudget` at constant level):

```
rowBudget n = 3 + [n = 0] + [n = 26] + 14·[n = 31]
sampler_length : (eval H (UnifiedSampler.samp p _ n P m).toProgram).1.length ≤ rowBudget n   -- every n, every message
row_length     : (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1.length ≤ rowBudget n
budget_sum     : ((List.range 33).map rowBudget).sum = 115
transcript_length : (chains 0..32).flatten.length ≤ 115
verifier_length   : (terminal ≤ B) → (eval H (OracleDecisionFeasibilityCore.verifier D dO pub pf)).1.length ≤ 115 + B
OraclePortExperiment.Budget dO := ∀ H p m, (eval H (dO p m)).1.length ≤ 1046
OraclePortExperiment.verifier_budget : Budget dO → … ≤ 1161
OraclePortExperiment.first_reads : AdversaryQueries P Q → Budget dO → firstReads emptyTable (eval H (recorded D dO P)).1 ≤ Q + 1161
```

Aspis (`AspisRec40CallBudget`):

```
row_length        : (eval H ((AspisRows40.Protocol.protocol D).chain H pub pf n).toProgram).1.length ≤ rowBudget n
                    -- R1's row_length through Protocol.chain_eq; not re-proved
budget_sum        : ((List.range 40).map rowBudget).sum = 136
budget_split      : … = ((List.range 33).map rowBudget).sum + 7 * 3
transcript_length : (chains 0..39).flatten.length ≤ 136
sampler_verifier_length : (eval H (AspisRows40.Starts.verifier D d pub pf)).1.length ≤ 136
verifier_length   : (terminal ≤ B) → (eval H (AspisRec40.Decision.verifier D dO pub pf)).1.length ≤ 136 + B
Budget dO B := ∀ H p m, (eval H (dO p m)).1.length ≤ B            -- R1's, with the bound a parameter
verifier_budget   : Budget dO B → … ≤ 136 + B
firstReads_le_length                                              -- re-proof of R1's generic lemma
                                                                  -- (which is in R1VerifierCallBudget, class iii)
firstReads_eq     : copy of OracleDecisionFeasibilityCompiler.firstReads_eq (40-row verifier)
first_reads       : AdversaryQueries P Q → Budget dO B →
                    firstReads emptyTable (eval H (AspisRec40.Decision.recorded D dO P)).1 ≤ Q + (136 + B)
projected_first_reads : (∀ s, Budget (d s) B) → (∀ H, (eval H P).1.length ≤ Q) →
                    firstReads emptyTable (eval H (AspisRec40.HitMass.projected D d P)).1 ≤ Q + (136 + B)
```

`projected_first_reads` is new in form. It is the bound for the full
stored-input experiment with the decision as a parameter. R1 states its
counterpart only inside the two-transaction module (`OraclePortFrozen2.distinct_bound`).
The proof here is direct. The full trace is the prover's trace, one verifier
run, and the same run again (`projected_trace_eq`, via the decision
verifier's enrichment invariance). The repeat adds no distinct reads
(`OracleProgramRecording.firstReads_repeat_suffix`).

Instance at the one-transaction game agent's decision (`AspisRec40CallBudgetAspis`).
Its `AspisOneTx.decision_budgetS` is exactly `∀ s, Budget (dV_aspis s) 975`
(`dV_aspis_budget`). So:

```
AspisRec40.CallBudgetAspis.verifier_issued       : (eval H (Decision.verifier D (dV_aspis s) pub pf)).1.length ≤ 1111
AspisRec40.CallBudgetAspis.projected_first_reads : firstReads emptyTable (eval H (projected D dV_aspis P)).1 ≤ Q + 1111
```

These were compiled against the `AspisOneTxDecision` object present on the
build host at PSD-35.

### 6.2 The count, and how the parts add up

The paper count of 136 is confirmed: 33 × 3 + 1 (row 0's initialization
frame) + 1 (row 26's opening reseed frame) + 14 (row 31's query chain: eight
squeeze/advance pairs after the absorb, 17 calls) + 7 × 3 (rows 33–39, each
absorb, squeeze and advance) = 136. Every row bound holds on every input,
malformed messages included (R1's `sampler_length`).

R1: 1,161 = 115 (transcript) + 1,046 (decision), and the decision is
477 (batch 0) + 563 (batch 1) + 6 (checkpoint reads).
Aspis: 1,111 = 136 (transcript) + 975 (decision). The decision is the three
merged multiproofs only (`mergedAll_budget`), and there are no checkpoint
reads, because `dV_aspis` reads no checkpoint and the one-transaction verifier
has none. The seven new rows move from "after the checkpoint" into the
transcript part: they add 21 to the transcript count, and the decision no
longer contains them. Nothing else issues digest calls in the model verifier.
The bound needed for the terminal decision is `∀ s, Budget (d s) 975`, which
`decision_budgetS` provides.

### 6.3 A refinement point found while doing this: call order

In the model (R1's and this copy), the verifier first runs all transcript
rows and then the terminal decision. In R1 that is also the source order.
In Aspis it is not. `fused.rs::verify_summed` (lines 495–512) runs
`prepare` (rows 0–32), then `batch_merkle(…, 0)` and `batch_merkle(…, 1)`
(the merged Merkle digests), then `summed_final_checks` (rows 33–39). So the
Rust issues the Merkle digests before rows 33–39, and the 40-row model issues
them after.

The counts above do not depend on the order: they are sums over the same
calls. The prefix and start arguments do depend on it. `chronological_prefix`,
`hit_mass` and the charged experiment assume that the 40 sampler rows come
before every terminal read. A source refinement of the Aspis verifier
therefore needs one of two things:
- a transport argument for that reordering, i.e. that the transcript rows
  33–39 do not depend on the Merkle digests' answers (AGENTS.md §4 requires
  this to be proved, not assumed);
- or a model with the Rust order.

Nothing here assumes either. The point is recorded for the one-transaction
game agent and the source-refinement work.

### 6.4 Validation

| Attempt | Module | Source sha256 | Exit | Wall | Peak RSS (time) | cgroup peak | Axioms |
|---|---|---|---|---|---|---|---|
| PSD-33 | AspisRec40CallBudget | efae0c78…42a68189 | 0 | 2.72 s | 4,212,008 KB | 431,751,168 B | 10× [propext, Classical.choice, Quot.sound], 1× [propext, Quot.sound], 2× [propext] |
| PSD-34 | AspisRec40Measure3 (measurement only) | aeb94a43…a1f981 | 0 | 2.16 s | 4,228,104 KB | 443,543,552 B | none (no theorems) |
| PSD-35 | AspisRec40CallBudgetAspis | c6bf2d24…dcf88d9 | 0 | 3.54 s | 4,215,524 KB | 417,832,960 B | 3× [propext, Classical.choice, Quot.sound] |

PSD-34 walks the constant dependencies of `projected_first_reads`,
`first_reads`, `sampler_verifier_length` and `hit_mass`: 250 modules and
1,166 constants, with **0 class (iii) modules**. `R19BudgetSamplerReads`
(class ii) is reached, through R1's `sampler_length`.

## 7. The clean event: measurement and statement (step 2; nothing in step 3 is copied yet)

### 7.1 Measurement

R1's clean event is `Frozen2StartChargeClean.clean`; `failure_bound`
consumes it through `CleanAcceptedModel`. Two measurement files (each proves
nothing) walk the constant dependencies, expanding through the 555
changed-dependent or class (iii) modules:
- `AspisRec40Measure4.lean` (PSD-36) walks the whole event.
- `AspisRec40Measure5.lean` (PSD-37) walks each ingredient of R1's proof
  separately. Every module is assigned to the first ingredient that reaches
  it, in the order listed below.

Result: `clean` reaches 251 modules, 237 class (ii) and 14 class (iii).
`failure_bound` reaches 39 more, all class (ii) (extractor, envelope and
density modules, which belong to the acceptance-link agent's assembly).

| Ingredient of R1's proof | Modules (exclusive) | Disposition for Aspis |
|---|---:|---|
| H. Definitions: `CleanAcceptedModel`, `bad`, `projected`, and through `dV_frozen2` its decision | 99 (10 iii) | **(i)** 75: R1's decoder chain inside `decFinal`, the classifier-density modules, the `R1Literal*`/`R1Unified*` decoders, `D0*`, `Literal*`, word builders. **Done elsewhere**: `projected` (AspisRec40HitMass), `dec`→`decFinal`, classifier→`classifier40` (PSA), `Checks`→`AspisChecks` (PSA), `admit`/`D0ScheduleAdmission`→`admitS` (game), `OraclePortStoredDecisionDraftC4`/`ParserC4`→`parseReachedS` (game), `dV_frozen2`→`dV_aspis` (game). **(ii)** 3: `CleanAcceptedModel`, `bad` and `clean` → `CleanAcceptedModel40`, `bad40`, `clean40`. **(iii)** 10, below |
| E. Prefix: `same_transcript`, `chronological_prefix`, `recovered_eval`, `first_reads` | 15 (3 iii) | **Done**: `chronological_prefix`, `recovered_eval` (HitMass); `first_reads` → `projected_first_reads` (CallBudget, `Q + 1111`). **(ii)** 1: `same_transcript` (it needs `words_prefix`, i.e. the frame lemmas `OraclePortReplay.frameFromView_eq`, `RawCutWordsFromView.{frameFromView_eq, frame_read}` for the 40-row run; only rows 0, 2 and 30 are read, delegation through `chain_eq`). **(iii)** 3, below |
| D. Format: `RWireCheckedFormat.format_of_checks`, `format_of_enrich` | 11 | **(i)** 10. **(ii)** 1: `format_of_checks` from `AspisChecks`. R1's needs R1's `Checks`, but it uses only `data`, `matchingRead`, the row-31/32 entries and their validity (`checks_force_constructor_schedule`), and `AspisChecks` has each of these on `rs.take 33`. This copy matters: R1's `Checks` can be had from `AspisChecks` only together with no-hit (`aspis_checks_noHit_r1_checks`), and the format is needed before the no-hit is known |
| C. Tag: `OraclePortAdmission.accepted_tag`, `admitted_dV` | 1 | **(i)** `InitialTagDecision`. **(ii)** 1: `accepted_tag` with `admitS` (game: `admitted_aspis`, `accepted_guardS` give `Guard (take33 tr)`) |
| B. Words: `OraclePortCleanModel.extractor_word_alignment` | 8 | **(ii)** 1: the alignment for the 40-row run (`wordsFromRun` of the recorded run equals that of the original, and the words are fixed). It reads rows 0, 2 and 30; the frame modules (`RawCutCommitmentFrames`, `RawCutLiteral*Successor`, …) are **(i)** |
| G. Hit: `Frozen2StartChargeCompletion.hit_in_prefix` | 1 | **(ii)** 1: 40 rows (`StartChargeHit.hit_implies_chain` is generic in the protocol, **(i)**). It needs `transcript_start_read` for 40 rows (frame read of the charged run) |
| F. Decodes: `Frozen2StartChargeCompletion.decodes` (`RWireRawFullPublicRun.adaptive_run_decodes_and_follows`, rows < 33) | 82 | Rows 0–32: **(i)** 82, plus **(ii)** 1 transport lemma. The Aspis base trace is R1's base trace followed by the chains of rows 33–39 (`FS2.verifier_eval` and `chain_eq`), so R1's no-collision and query hypotheses pass to the prefix, and `decFinal = dec` wherever `dec` decodes (`decAspis_of_r1`). Rows 33–39: **(iv) new content**, below |
| A. Checks: `OraclePortFrozen2Consumer.fibre_checks` through `OraclePortFrozen2C6.checked_acceptance` | 34 (1 iii) | **Game agent**: M6 and M8 done (`accepted_checks_aspis`); M7 (`Reached`, `Roots.targets`, `maps_eq_builder` on `AspisRec40.Decision.original`) and M9 (`CheckedAcceptance40`, `fibre_checks`) in progress. The clean event takes M9's result as a hypothesis (7.2) |

**Class (iii), all 14**, with what each is used for and what replaces it:

| Module | Used for (constants reached) | Aspis |
|---|---|---|
| `OraclePortFrozen2Decision` | `dV_frozen2`, `batch`, `batch0`, `afterBatch0`, `stage2`, `batch1` | `dV_aspis` (game, done) |
| `OraclePortFrozen2Checkpoint` | `checkpoint`, `finish`, `checkpoint_reads` inside `afterBatch0` | none: no checkpoint |
| `OraclePortCheckpointStateC3`, `…AbiC5`, `…OracleC5`, `…PreparedC5`, `…ResumeC5` | the saved-state ABI, writer/resumer and query decoding used by `dV_frozen2`'s checkpoint step | none |
| `OraclePortCheckpointSlicesC5` | checkpoint slice lemmas used by `OraclePortFrozen2.decision_budget` | none |
| `R16DecisionCheckpoint`, `R16DecisionQueryModel` | the TX2 decision and query model in `dV_frozen2`'s definition | none (`dV_aspis` is direct) |
| `OraclePortAcceptedContextC6` | `context`, `coordinates` of the stage-2 decision | none (`parseReachedS`) |
| `OraclePortFrozen2Bounds` | `decision_budget` 1,046 | `decision_budgetS` 975 (game, done) |
| `R1VerifierCallBudget` | `firstReads_le_length` | re-proved in AspisRec40CallBudget (done) |
| `OraclePortFrozen2Trace` | `accepted_trace`, `old_read`: the accepted run's reads, in `fibre_checks` | M7 (`Reached` on `Decision.original`) |

**Counts, Aspis side.**
- (i) reused unchanged: about 180 of the 237 class (ii) modules.
- (ii) copies, mine: 7–9 modules, namely `clean40` with `accepted_facts40` and
  `CleanAcceptedModel40`/`bad40`, `same_transcript40` with the frame lemmas,
  `format40`, `tag40`, `wordAlignment40`, `hit_in_prefix40`/`decodes40`, and the
  rows-0–32 transport.
- Copies or new content by the game agent: 34 (M7, M9).
- (iii) counterparts: none to copy. 13 are replaced by `dV_aspis` or by
  nothing; `OraclePortFrozen2Trace` is replaced by M7.
- (iv) new content, mine: the decoding completeness of rows 33–39 (estimated
  4–8 modules, section 7.3).

### 7.2 The statement

Definitions compiled in `AspisRec40CleanStatement.lean` (PSD-38, exit 0):
`CheckedAcceptance40`, `compiledRows40`, `CleanAcceptedModel40`, `bad40`,
`FinalDecodes`.

R1:

```
theorem Frozen2StartChargeClean.clean (D) (P) (Q) (hq : ∀ H, (eval H P).1.length ≤ Q) :
  CleanAcceptedModel D (projected D P) (bad D P Q)
CleanAcceptedModel D exp hit := ∀ H, let run := eval H exp; run.2.2 = true → ¬ hit run →
  ∃ _ : LiteralAcceptanceTerminal.Checks run.2.1.1 ((LiteralByteProtocol.protocol D).transcript H run.2.1.1
      (proof (wordsFromRun run) run.2.1.2) 33).rounds,
    ¬ GenericNoHit.hitFrom LiteralClassifier.bad run.2.1.1 [] (… 33).rounds
bad D P Q run := binaryCollision (Q+1161) run ∨ prefixHit D P run
```

Aspis (to be proved in `AspisRec40Clean`):

```
theorem clean40 (D) (P) (Q) (hq : ∀ H, (eval H P).1.length ≤ Q)
    (hchecks : ∀ s, CheckedAcceptance40 D (AspisOneTx.dV_aspis s)
        (OraclePortStoredReductionC7.pairProver s P) (Q+1111))                 -- from the game agent (M9)
    (hfinal : ∀ H,                                                          -- mine, section 7.3
        firstReads emptyTable (eval H (AspisRec40.ChargePrefix.base D P)).1 ≤ Q+1111 →
        ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
            BinRawByteCollisionTargets.pred (Q+1111)) emptyTable (eval H (AspisRec40.ChargePrefix.base D P)).1 →
        RWireCheckedFormat.Format (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 →
        (eval H (AspisRec40.ChargePrefix.base D P)).2.1.1.tag = 2 →
        FinalDecodes D H (eval H (AspisRec40.ChargePrefix.charged D P))) :
  -- the four premises of hfinal are exactly those of R1's
  -- Frozen2StartChargeCompletion.decodes (hQ, hout, format, tag)
  CleanAcceptedModel40 D (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P) (bad40 D P Q)
```

Every difference from R1:
1. `Checks` on 33 rounds becomes `AspisChecks decodePairS` on 40 rounds, and
   `LiteralClassifier.bad` becomes `AspisAcceptance.bad decodePairS`. This is
   the form `AspisAcceptance.aspis_relation` consumes, with
   `pf := proof (wordsFromRun run) run.2.1.2`.
2. `projected D P`, with R1's fixed `dV_frozen2`, becomes
   `HitMass.projected D dV_aspis P`.
3. `Q + 1161` becomes `Q + 1111` (`CallBudgetAspis.projected_first_reads`).
4. The prefix hit uses `decFinal` and `classifier40 decodePairS`.
5. **Two hypotheses that R1's statement does not have:**
   - `hchecks` is R1's `fibre_checks` (proved inside R1 from the
     two-transaction chain). For Aspis it is the game agent's M9 result, with
     exactly the shape of R1's `OraclePortConsumer.CheckedAcceptance`
     (definition `CheckedAcceptance40`): no collision on the recorded run plus
     acceptance of the original run give `AspisChecks` on the recorded run's
     40 rows. It is a hypothesis only until M9 lands; then it is discharged,
     not kept.
   - `hfinal` is the rows-33–39 part of R1's `Frozen2StartChargeCompletion.decodes`.
     It is mine (7.3) and is also discharged, not kept.

   Neither is a new assumption of the final result. The final clean event is
   R1's with no extra premise once M9 and 7.3 are in.

**What M7 must give for `hchecks`.** M9 builds `hchecks` from
`accepted_checks_aspis` instantiated at the actual run. The hypotheses of
`accepted_checks_aspis` that M7 supplies, on the run
`eval H (AspisRec40.Decision.original D (dV_aspis s) (pairProver s P))`:
- `parsed : parseReachedS stored tr = some p` and
  `query : queries (take33 tr) = some q`, for the run's erased 40-round
  transcript `tr`, and `accepted`. These are copies of
  `OraclePortFrozen2Reached.accepted`.
- `log` = the run's trace, with `consistent` and `contains` (the merged slot
  reads are in the log). Copies of `Reached.{slots_read, consistent}`.
- `bound : firstReads emptyTable log ≤ Q + 1111`. This is
  `CallBudget.first_reads` / `projected_first_reads`, mine and done.
- `clean`: no collision on the log, from the hypothesis of `CheckedAcceptance40`.
- `frames k` = first cells of rows 0, 2 and 30, with `frameRead` and
  `rootRead`. Copies of `OraclePortFrozen2Roots.targets` and
  `Reached.frame_read`.
- To turn the conclusion's
  `reword (maps log frames p) (typedRows p q tr)` into `compiledRows40`:
  a copy of `OraclePortFrozen2ActualChecks.maps_eq_builder` (recovered maps =
  `wordsFromRun`).

### 7.3 New content: decoding completeness of rows 33 to 39

R1's clean event charges a classifier hit at a submitted row to the decoded
start of that row (`hit_in_prefix` through `Decodes`). For Aspis, a hit at
rows 33–39 has to be charged the same way. That needs: on the actual charged
run, with no collision, the absorb frame of row n (33 ≤ n < 40) is decoded
by `decFinal` at the table before it, and `bfollow` of its output follows the
trace to the true (prefix, message, challenge).

Ingredients:
- `FinalByte.select n` and `Context.parse` succeed on the actual table. This
  uses `DuplexSeek.seek_of_noColl` for the one-step walks, and R1's row-32
  facts at the actual run: `JointContext.parse` with 31 records and
  `FullPublicSelection.select` at row 32's frame, which R1 obtains inside
  `adaptive_run_decodes_and_follows`. These must be shown to persist at the
  larger table before row n's frame, under no collision.
- The follow of `Final.output`: the pending squeeze answers of rows 32..n−1 are
  recorded from the trace, and R1's 32-round prefix completion is R1's
  (`R1JointActualView`, `RWireRawLiteralDecoderCompletion`).

This was earlier deferred as "honest-run copies". The clean event cannot do
without it: without it a classifier hit at rows 33–39 is not charged. It is
not a weaker event and not an assumption; it is a proof obligation in my own
files.

### 7.4 Validation

| Attempt | Module | Source sha256 | Exit | Wall | Peak RSS (time) | cgroup peak |
|---|---|---|---|---|---|---|
| PSD-36 | AspisRec40Measure4 (measurement) | e96b4633…6b208cb | 0 | 4.34 s | 4,223,240 KB | 428,572,672 B |
| PSD-37 | AspisRec40Measure5 (measurement) | 862f3cea…bc8721 | 0 | 4.62 s | 4,225,668 KB | 429,907,968 B |
| PSD-38 | AspisRec40CleanStatement (definitions) | 3c3fcfb2…53dd837 | 0 | 2.95 s | 4,218,656 KB | 429,699,072 B |

No theorems in these three files, so no axioms printed.

## 8. The clean event: step 1 compiled, `hchecks` discharged, `hfinal` open

### 8.1 What compiles

| Module | Content (R1 statement copied) |
|---|---|
| `AspisRec40Frames` | 40-row replay and frame lemmas: `lift_verifier` (the always-true decision verifier is `Starts.verifier`), `sampler_reads`, `transcript_eq_of_agrees`, `recorded_transcript_eq`, `frameFromView_eq`, `frame_read`, `commitment_cut_eq`, `wordsFromRun_compiled_eq_original`, `output_pair`, `base_lift`, `words_prefix` (copies of `OracleDecisionFeasibilityCore.lift_*`, `OraclePortReplay.*`, `RawCutWordsFromView.*`, `OraclePortWords.*`, `OraclePortSamplerPrefixDraft.*`, 33 → 40) |
| `AspisRec40CleanRun` | `base_split`/`charged_split` (the Aspis base and charged runs are R1's followed by the chains of rows 33–39, same output); `words_base_eq`; `decodes_r1rows` (R1's `Frozen2StartChargeCompletion.decodes` for rows 0–32, transported to the longer trace and to `decFinal`); `Decodes40`, `decodes40` (rows 0–32 from R1, rows 33–39 from `FinalDecodes`); `chains_read`, `charged_reads`; `hit_in_prefix` (copy of R1's, through the generic `StartChargeHit.hit_implies_chain`) |
| `AspisRec40CleanA` | `projected_eq_recorded` (the full experiment equals the recorded decision experiment at the run's own stored input: this is the 40-row selection step, R1's `annotated_selected` + `fibre_prover`), `recorded_accepts`, `same_transcript` (copy of R1's), `original_accepts` |
| `AspisRec40CleanB` | `schedule_of_matching` (copy of `RawChecksConstructorSchedule.checks_force_constructor_schedule` with its two read fields as arguments), `valid_of_checks`, `format_of_checks` (copy of `RWireCheckedFormat.format_of_checks` from `AspisChecks` fields) |
| `AspisRec40CleanWords` | `extractor_word_alignment` (copy of `OraclePortCleanModel.extractor_word_alignment` with `AspisChecks`) |
| `AspisRec40CleanTag` | `guard_tag`, `tag_of_admitS`, `accepted_tag`: the public tag from `admitted_aspis` and `accepted_guardS`. Only the guard's first conjunct (the statement's tag, on the first 33 rounds) is used; nothing about rows 33–39 is taken from admission (reviewer's caveat) |
| `AspisRec40Clean` | `accepted_facts` (copy of R1's, under `hchecks`), `clean40` (copy of R1's `clean`), `hit_in_prefix_of` (the hit step alone) |
| `AspisRec40CleanJoin` | `checks_of_fibre`: `hchecks` from the game agent's `AspisOneTx.Checked.fibre_checks40` and R1's `Frozen2StartChargePrefix.fibre_prover` (`pairProver s P = prover P`); `accepted_checks40 : AspisFailureBound.AcceptedChecks40 D P Q` and `word_alignment40 : AspisFailureBound.WordAlignment40 D P Q` under R1's query hypothesis only; `hit_in_prefix40 : AspisFailureBound.HitInPrefix40 D P Q` under `hfinal` |

Join shape: option (a) of the coordinator's message. The three definitions
of `AspisFailureBound` are proved as stated, at `expE D P` (the same program
as `HitMass.projected D dV_aspis P`, already declared at R1's `Experiment`
type). No bridge lemma is needed: the decision argument, the prover wrapper
(`pairProver` to `prover`, by R1's `fibre_prover`) and the carrier type
agree. `AcceptedChecks40` and `WordAlignment40` are proved outright.
`HitInPrefix40` has one hypothesis left, `hfinal`.

The lift from the fixed-proof statement to the full experiment (the
reviewer's question) is `AspisRec40.CleanA.projected_eq_recorded`, used in
`AspisRec40.Clean.accepted_facts`. R1's own selection step goes through
`OraclePortStoredReductionC7.annotated_selected`; this proof computes the
evaluations directly.

Constant-level audit (`AspisRec40Measure6.lean`, PSD-70; 597 modules,
3,523 constants, roots `accepted_checks40`, `word_alignment40`,
`hit_in_prefix40`, `clean40`, `ChargePrefix.starts`, `verifier_starts`):
one class (iii) module is used, `R1VerifierCallBudget`
(`firstReads_le_length`). It enters through the game agent's
`AspisOneTxRun` (line 107), reached via `fibre_checks40`. The same generic
lemma is re-proved in `AspisRec40.CallBudget.firstReads_le_length`, and
switching to it removes the use. `OraclePortFrozen2Resource`,
`Frozen2StartChargeCompletion` and `Frozen2StartChargePrefix` (class ii)
are also reached.

### 8.2 `hfinal`: the three sub-results, each next to the R1 row-32 analogue

Let `tr` be the Addr-level trace of the actual 40-row run, `c_n` the absorb
frame of row n (33 ≤ n < 40), `T_n = tableBefore emptyTable tr c_n`, and
no collision on `tr`.

1. **Context recovery at the later table.**
   `Context.parse p pub.pubBytes pub.tag n c_n T_n = some ⟨jc, a32, tail, x, m⟩`,
   with `jc` the actual row-32 context.
   R1 analogue: `UnifiedRhoInjection.decodes_and_follows`'s
   `hcontext : JointContext.parse … c T_32 = some ctx`, built from
   `QueryFirstRead.recover_query_before_endpoint` and
   `OpeningQueryTrace.recover_and_follow`.
   The typed prefix walk `OpeningPrefixAnchor.walk_before_anchor` takes the
   anchor as a parameter, so it applies at anchor `c_n` (`T_n`) unchanged.
   The seeks (the query chain from row 32's endpoint, and one advance step
   for each of rows 32..n−1) come from the generic
   `DuplexSeek.seek_of_noColl` at `T_n`.
2. **Selection at the later table.** `FinalByte.select n c_n T_n = some pub`.
   R1 analogue: `RWireRawFullPublicRun.select_actual_run` at row 32, through
   `RawLatePublicSelector.select_of_joint_context` and
   `RawPublicOpeningAnchor.walk_before_anchor` (anchor-parametric).
3. **Follow.**
   `bfollow (Final.output …) (traceFrom tr c_n) (QueryNextLaw.own p c_n) ((Final.missing p T_n ctx).map …) T_n = some (transcript n, msg n, chal n)`.
   R1 analogue: `JointNextTrace.follows_after_prefix_query` (row 32, pending
   = R1's joint missing cells). New content: the pending squeeze cells of
   rows 32..n−1 and the completed later rounds.

Also needed: the byte-to-Addr bridge for the 40-row run. R1's
`RWireRawLiteralDecoderRestore.decodes_and_follows` /
`RWireLiteralLegacyDecoderCompletion` / `UnifiedPrefixedReads` cover 33 rows,
and the byte-level collision event has to be translated to `badColl` and
`ParsedStateCollision`. None of these needs a two-transaction module, a
weaker event or an extra premise. The premises are R1's four (`hQ`, `hout`,
`format`, `tag`). This is the remaining work: an estimated 10–15 modules,
the follow (3) being the main new proof.

### 8.3 Lessons (heartbeat and kernel timeouts)

Several attempts timed out (PSD-44, 47, 49–53, 58, 60, 63). Each time the
cause was a reduction of `.statement` of a concrete 40-round transcript,
through a `show`/`change`, a `dsimp` of `erasePrefix`, or the kernel's eager
projection reduction (PSD-63: `(kernel) deterministic timeout`, 7.05 GB).
The fix is to keep the transcript abstract:
- a lemma stated for an arbitrary erased prefix (`guard_tag`);
- R1's own `InitialTagDecision.erased_transcript_tag` after
  `Protocol.transcript_eq`;
- `generalize` before any projection.

No limit was raised.

### 8.4 Validation

| Attempt | Module | Source sha256 | Exit | Wall | Peak RSS (time) | cgroup peak | Axioms |
|---|---|---|---|---|---|---|---|
| PSD-40 | AspisRec40Frames | 9da2706650d0817553b1e4d195c3677fbb0788f0036e2d2638e123430960a778 | 0 | 4.20 s | 4,216,572 KB | 437,661,696 B | 11× [propext, Classical.choice, Quot.sound] |
| PSD-43 | AspisRec40CleanRun | 2f43921b16c52acd995ce8cca130334a2846f14ef2446755f7bee7f2b71dcb2a | 0 | 4.94 s | 4,241,396 KB | 438,890,496 B | 8× standard three |
| PSD-62 | AspisRec40CleanA | 148bf2dea5843a7d94a4d883f602c60f1f0a8b28f2421e5aada5c30c9063f499 | 0 | 1.81 s | 4,227,688 KB | 430,227,456 B | 4× standard three |
| PSD-46 | AspisRec40CleanB | e9a1fa0f7a0d026e5bb5f666cb3033496faec6bcd175a9fa3b598e7212c481dc | 0 | 5.74 s | 4,254,968 KB | 458,522,624 B | 3× standard three |
| PSD-48 | AspisRec40CleanWords | 85ce93da9cb35896926f6bea8d6a55e52e1087f0e9ef79551aa668c8dc16a5ef | 0 | 3.62 s | 4,231,364 KB | 425,971,712 B | 1× standard three |
| PSD-65 | AspisRec40CleanTag | 8973ca6b3b933ad62282691f6ece44a99ca255c5e47d180015fe8b0dcf5fdbd4 | 0 | 1.68 s | 4,249,796 KB | 431,435,776 B | 3× standard three |
| PSD-68 | AspisRec40Clean | b33eb6b5988b4b1eb3b74018ade126048760ff0ae322605865b2f77f2cfc97fe | 0 | 2.00 s | 4,263,720 KB | 436,998,144 B | 3× standard three |
| PSD-69 | AspisRec40CleanJoin | 695c79cc89487a90f1b1eef54f19acaa4eaefebc25fde422904ac85a910e8041 | 0 | 1.83 s | 4,257,968 KB | 430,977,024 B | 4× standard three |
| PSD-70 | AspisRec40Measure6 (measurement) | 8738c9f8211477e9d00d1a7176c2a5678888ff68be58c8c0cd2301440d281fc7 | 0 | 2.22 s | 4,299,160 KB | 446,128,128 B | none (no theorems) |

All hashes were copied from the receipts' stdout.log and checked against
the masters. `AspisRec40CleanStatement` (PSD-38) is unchanged. No `sorry`,
no new axioms.
