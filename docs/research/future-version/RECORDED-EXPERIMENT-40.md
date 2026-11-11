# The recorded/charged experiment for the Aspis 40-row protocol (plan item 13)

Status: the measurement is done (section 1). The charged experiment and its
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
| PSD-26 | AspisRec40ChargePrefix | 862c6c83…7c9a9750 | 0 | 3.71 s | 4,208,628 KB | 430,391,296 B | 3× [propext, Classical.choice, Quot.sound] |

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
