# The Aspis 40-row instance: measurement, the acceptance-to-extraction link, and the file plan

Status, 2026-11-11. Reading and statements only; no new proof in this note.
"R1" is the two-transaction verifier, "Aspis" the one-transaction verifier.
Sources: the L187 release closure (read-only copy of its 13,552 sources).
Nothing here is a bound for Aspis; the release target is unchanged and not
yet established.

## 1. Measurement of the charged/recorded-experiment family

### 1.1 Method

Three roots, each with its import closure inside L187
(`tools/closure.py`):

- the bound layer: `Frozen2StartChargeProbability` (holds
  `restricted_union_bound` and `failure_bound`): **1,031** modules;
- the numeric total: `RPz7_F3T_Numeric`: 2,747 modules;
- the headline: `TAS_FinalB` (`deployed_splitB`, `deployed_charge`): 13,545
  modules, i.e. essentially all of L187.

`tools/between.py` then takes the modules of each closure that themselves
depend on `Frozen2StartChargeProbability` (the part "above" the restricted
bound). `tools/classify.py` assigns each module one class by searching its
code (comments stripped) in this order:

- (iv) source refinement: imports an extracted-source library (Aeneas, the
  `AspisR1*` extraction roots, the `N*_Ref*`/`Op*_Extract` references), or
  names `Aeneas`, `Extracted`, `Realizes`, `AdapterRw`, `Port26`, `Poseidon`;
- (iii) two-transaction game: names a checkpoint, `tx1`/`tx2`/`TX1`/`TX2`,
  `Stage1`/`Stage2`, `SCE_Experiment`, `Runs`, `AccountExperiment`, the
  `ARX_`/`ART_`/`ARQ_` account-run families, `resume`, `QvStage`;
- (ii) R1 33-row instance: names `LiteralClassifier`, `UnifiedSampler`,
  `SelectedTranscriptParams`, `LiteralByteProtocol`, `LiteralTranscript`,
  `UnifiedDecoder`, `UnifiedLabels`, `RecordedBinaryExperimentBin`, `RawCut`,
  another `Literal*` object, or the numbers 33/34;
- (i) otherwise (generic, or about objects Aspis shares unchanged).

`tools/dependent.py` gives a second, sharper measure for the bound layer:
which modules import (directly or transitively) one of the five R1
definitions the Aspis instance replaces (`R1UnifiedSampler`,
`R1LiteralClassifier`, `R1UnifiedDecoder`, `R1LiteralByteProtocol`,
`R1UnifiedLabels`). A module that does not is reusable unchanged.

Spot check by reading (headers and first definitions), 30 modules across the
classes: the heuristic is right for the bound layer except that comments
mentioning Pool or Rust caused false (iii)/(iv) before comments were stripped
(fixed in the counts below). It is weaker above the bound: 26 modules it puts
in (ii) are in fact the two-phase game and account run by name and content
(`SCE_*`, `SCF_*`, `SCG_*`, `P2P_*`, `F3T_AccountCharge`, `F3U_AccountEvent`,
`F3T_Runtime*`, `F3U_Runtime*`, `F3U_TwoPass`,
`OraclePortHeadlineFrozen2PerAttempt`, read: e.g. `F3T_AccountCharge` is the
`Q+2965` account mass over `R9PoolRuntimeBinding` inputs,
`OraclePortHeadlineFrozen2PerAttempt` is "Two-transaction per-attempt
endpoint ... includes the six checkpoint reads"). The counts below are the
script's; the corrected figures are given beside them.

### 1.2 Counts

| Layer | Modules | (i) generic/shared | (ii) R1 instance | (iii) two-tx game | (iv) source |
|---|---:|---:|---:|---:|---:|
| bound layer (closure of `Frozen2StartChargeProbability`) | 1,031 | 546 | 412 | 32 | 41 |
| from `failure_bound` to `F3T_Numeric.total` | 4 | 0 | 4 (all four are two-tx per-attempt endpoints by reading: (iii)) | — | — |
| above the bound, up to the headline | 6,885 | 360 | 57 (31 after moving 26 to (iii)) | 146 (172 corrected) | 6,322 |

Sharper measure for the bound layer: **582** of 1,031 modules do not depend
on any replaced definition and are reusable unchanged; **449** do (by class:
377 (ii), 27 (iii), 31 (i), 14 (iv)). Of the 449, **217** name a
whole-protocol object (`LiteralByteProtocol.protocol`/`rows`,
`LiteralClassifier.bad`/`budget`, `UnifiedDecoder.decode`,
`RawUnifiedDecoder.decode`, `RecordedBinaryExperimentBin.dec`) or hard-code
33/34 in code (155 do the latter); these need Aspis counterparts. The other
**232** reach a replaced definition only through facts about individual rows
(the semantic, circle, opening and query decoders and their laws).

What this says about the size of the Aspis bound layer:

- If the Aspis sampler, decoder and classifier are defined so that rows 0–32
  are R1's (definitional delegation, with lemmas `aspisSamp i = samp i`,
  `aspisDecode` dispatching to `UnifiedDecoder.component` for labels < 33,
  `aspisBad P m c = LiteralClassifier.bad P m c` for rounds < 32), the 232
  row-local modules are reused through those lemmas and the work is bounded
  by the **217** whole-protocol modules, many of which are thin (dispatchers,
  wrappers, the start-charge prefix, the clean event, the recorded and
  compiled experiment). This is the design the plan below assumes.
- If instead the instance is defined from scratch, all **449** need copies.
- Above the bound, the headline is overwhelmingly source refinement (6,322)
  and two-transaction game (172); neither carries over. Aspis needs a
  one-transaction game and its own source refinement; only about 31 (ii)
  and 360 (i) modules above the bound are candidates for reuse, and the
  numeric path from `failure_bound` to the total is 4 modules, all
  two-transaction endpoints.

The full lists of classes (ii) and (iii) (bound layer with the dependency and
33/34 flags; the four numeric modules; the 203 above the bound) are in
`aspis-instance-module-classes.tsv` (647 rows). Class (iii) in the bound
layer (32): `DecoderInstanceBoundary`, `HchecksPublicComposition`,
`OraclePortAcceptedContextC6`, `OraclePortCheckpoint*` (7),
`OraclePortFrozen2{Bounds,Checkpoint,Decision,Trace}`, `OraclePortHeadline`,
`OraclePortJoinSplitCore`, `OraclePortPool`, `OraclePortSixSlotBudgetC3`,
`QvStage{1,2}Count`, `R16Decision{Checkpoint,QueryModel}`,
`R19BudgetOriginalReads`, `R1FinalSoundnessBinPerQuery{,R18}`,
`R1FinalSoundnessNumeric`, `R1VerifierCallBudget`, `R9Pool*` (3),
`SharedBinaryRecordGrammar`, `WireBindingRecordCodec` (two of these,
`DecoderInstanceBoundary` and `OraclePortJoinSplitCore`, are by reading
interface drafts rather than game-specific; the regex hit their comments'
neighbours in code).

Uncertainty that remains: whether the recorded/compiled experiment
(`RawCut*`, `RawRecorded*`, `Bin*`, `OraclePort*C4–C6`) is generic in the
protocol at the level of its statements. 117 of the 217 whole-protocol
modules are in those families; reading five (`RawCutProverCompiler`,
`RawRecordedOracleExtractionMassBin`, `Frozen2StartChargePrefix`,
`Frozen2StartChargeClean`, `OraclePortActualAcceptanceC6`) shows they are
stated for `LiteralByteProtocol.protocol D` with 33 rows, not for an arbitrary
protocol, so they are copies with a changed instance, not instantiations.

## 2. Design: from acceptance to extraction (statements only)

### 2.1 What R1 consumes

R1 (`R1LiteralAcceptanceTerminal`):

```lean
structure Checks (pub : LiteralTranscript.Public) (rs : TranscriptRounds) where
  decoded : R0P.Public SemanticPublicWire.M31
  view : LiteralOpeningView.View
  data : MatchingSupport.Data E
  publicParsed : SemanticPublicWire.parsePublic pub.pubBytes = some decoded
  matchingRead : LiteralMatchingData.read rs = some data
  openingRead : LiteralOpeningView.read rs = some view
  pairingChecks : LiteralPairingChecks.checks rs
  m31 : LiteralTranscript.Message
  queryBytes : List Nat
  state31 : State
  m32 : LiteralTranscript.Message
  rho : E
  state32 : State
  entry31 : rs[31]? = some (m31, (TranscriptView.Value.queries (.ok queryBytes), state31))
  entry32 : rs[32]? = some (m32, (TranscriptView.Value.ordinary rho, state32))
  valid31 : LiteralTranscript.valid 31 m31
  valid32 : LiteralTranscript.valid 32 m32
  queries : Fin 22 → Fin 262144
  queryDecode : LiteralQueryRead.decode queryBytes = some queries
  firstMatch : ∀ j, MatchingSupport.match0 data (queries j)
  residualBatch : ∑ j : Fin 22,
    (LiteralOpeningView.eK (SelectedChallengeMap.rhoOf rho)) ^ j.val *
      QueryResidualBridge.residuals data queries j = 0
  claim : E
  polynomials : Fin 10 → Polynomial E
  claimParse : claimOf (SelectedSemanticPrefixFacts.lift view.semantic) = some claim
  polynomialParse : semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic) = some polynomials
  semanticChecks : sumcheckChecksZ … claim … polynomials …

theorem checks_noHit_relation (decoder) (H) (pub) (pf)
    (checks : Checks pub ((LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub []
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds) :
    ∃ w, LiteralProtocol.relation pub w
```

and `conditional_d3` turns "accepted ⇒ Nonempty (Checks …)" into FS2's D3.
On R1's actual run the "accepted ⇒ Checks" step is
`OraclePortActualAcceptanceC6.accepted_checks` (accepted and
collision-clean ⇒ ∃ parsed, queries, `Nonempty (Checks …)` on the recorded
words).

Where the definitions point (read):

- `MatchingSupport.match0 d i := FirstFold.foldWord d.alpha0
  (TwoFoldExtraction.batchedWord d.W d.gamma) i = d.V i` (the first fold of
  the committed words equals the folded word at `i`);
- `QueryResidualBridge.residuals d q i := values d q i −
  ConcreteProjection.secondEncoder d.f (parentIndex (q i))` with
  `values d q i := curveValue (channels d.V) d.alpha1 (parentIndex (q i))`;
- `LiteralPairingChecks.checks rs` reads the round payloads and requires
  `SelectedOpeningPairing.coefficientChecks`, three conjuncts: (P1)
  `eval7 row30 α1 = RoundPairing.dot row31 (dualFold α1 (dualFold α0
  (weights F F0 κ))))` (R1's `pair == claim`), (P2) the round-1 boundary check
  against `eval7 row29 α0`, (P3) the round-0 boundary check against the
  initial claim;
- `LiteralMatchingData.read rs` builds `data` from rounds 25–31 only (opening
  view, staged rows, the row-31 final message, `vAt`, γ, κ, α0, α1 at rows
  27–30), and `LiteralRhoDensity.bad P v` is `rhoOf v ∈ QueryResidualBridge.rhoBad
  eK d q` with `(d, q)` read from `P.rounds` (`beforeRho`).

### 2.2 Field by field for Aspis

| Field | Aspis gives it |
|---|---|
| decoded, view, data, publicParsed, matchingRead, openingRead | directly: same bytes in rounds 0–31, same reads |
| m31, queryBytes, state31, entry31, valid31, queries, queryDecode | directly: row 31 unchanged |
| m32, rho, state32, entry32, valid32 | directly: row 32 unchanged (empty payload, ρ) |
| claim, polynomials, claimParse, polynomialParse, semanticChecks | directly: semantic layer unchanged |
| pairingChecks (P2), (P3) | directly: `finish_relation_round` on the same round polynomials |
| pairingChecks (P1) `S_W = claim` | only outside the bad events of rows 33–39: `AspisFinalSumcheckModel.stageCD_sound`, first conclusion, with `W := dualFold α1 (dualFold α0 (weights F F0 κ))`, `f := row31` |
| residualBatch | only outside the bad events of rows 32–39: `stageCD_sound`, second and fourth conclusions (`S_w = rhs2` and all second-fold residuals zero), with `B i j := QueryResidualBridge.basis q i j`, `G i := values d q i`; the sign flip `secondResidual = −residuals` is `NaturalEmbedding.secondEncoder_query_eq_natural_sum` (as in `QueryResidualBridge.residuals_eq`) |
| firstMatch | only outside the row-32 bad event of the residual PAIR: `stageCD_sound`, third conclusion (all first-fold residuals zero), with `r0 j := foldWord α0 (batchedWord W γ) (q j) − V (q j)`; this is where the pair-binding result enters |

### 2.3 The statement

New objects (names are plain, owners in section 3):

```lean
/-- First-fold residuals of the committed words at the queried positions. -/
def firstResiduals (d : MatchingSupport.Data E) (q : Fin 22 → Fin 262144) : Fin 22 → E :=
  fun j => FirstFold.foldWord d.alpha0 (TwoFoldExtraction.batchedWord d.W d.gamma) (q j) - d.V (q j)

/-- Row-32 bad set for the residual pair (≤ 21). -/
def pairBad (iota : K →+* E) (d : MatchingSupport.Data E) (q) : Finset K :=
  bad2 iota (firstResiduals d q) (QueryResidualBridge.residuals d q)
```

Named hypothesis supplied by the pair-binding piece (`AspisPairResidual*`),
the shape its deliverable must match:

```lean
theorem pair_queries_match (iota : K →+* E) (d : MatchingSupport.Data E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (hrho : rho ∉ pairBad iota d q)
    (h0 : ∑ j : Fin 22, (iota rho) ^ j.val * firstResiduals d q j = 0)
    (h1 : ∑ j : Fin 22, (iota rho) ^ j.val * QueryResidualBridge.residuals d q j = 0) :
    (∀ j, MatchingSupport.match0 d (q j)) ∧ (∀ j, QueryResidualBridge.residuals d q j = 0)
-- and pairBad_card : (pairBad iota d q).card ≤ 21
```

Aspis checks (the 40-round counterpart of `Checks`): every field of `Checks`
except `firstMatch`, `residualBatch` and `pairingChecks`, plus

```lean
  roundChecks : (P2) ∧ (P3)                        -- same bytes as R1
  firstBatch : ∑ j, (eK (rhoOf rho)) ^ j.val * firstResiduals data queries j = 0
  claimS rhs2 : E                                  -- the row-33 message
  entry33 : rs[33]? = some (m33, (.ordinary lam, state33)), m33 encodes (claimS, rhs2)
  claimDef : claimS = eval7 row30 α1                -- the claim the verifier computed
  rhs2Def : rhs2 = ∑ j, (eK (rhoOf rho)) ^ j.val * values data queries j
  rounds : Fin 6 → K × E × E                        -- rows 34–39: (r_b, c0_b, c2_b)
  entryRound : ∀ b, rs[34 + b]? = some (m_b, (.ordinary (r_b), _)), m_b encodes (c0_b, c2_b)
  finalCheck : finalClaim eK roundsList (claimS + eK lam * rhs2) =
    foldAll eK rs f 0 * (foldAll eK rs W 0 + eK lam * foldAll eK rs (qweight eK ρ B) 0)
```

The link (to write; model level, about the 40-round literal transcript):

```lean
theorem aspis_checks_noHit_r1_checks
    (pairMatch : pair_queries_match-shaped hypothesis, as above)
    (pub) (rs : TranscriptRounds) (hlen : rs.length = 40)
    (checks : AspisChecks pub rs)
    (hno : ¬ GenericNoHit.hitFrom AspisClassifier.bad pub [] rs) :
    Nonempty (Checks pub (rs.take 33)) ∧
      ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub [] (rs.take 33)
```

with `AspisClassifier.bad P m c` (the event reads the prefix AND the row's
own message, as the row-densities agent found: `claimS ‖ rhs2` is row 33's
payload, `c0_b ‖ c2_b` row 34+b's; both are fixed before the challenge by
`UnifiedSampler.unified_law`) equal to `LiteralClassifier.bad P m c` for
rounds < 32, `rhoOf c ∈ pairBad eK d q` at round 32 (with `(d, q)` from
`beforeRho P`), the combining-challenge event at 33 (`lambdaBad eK (S_W −
claimS) (S_w − rhs2)` with `S_W`, `S_w` from `beforeRho P` and ρ, `claimS`,
`rhs2` from the row-33 message) and the round events at 34–39 (`roundBad eK
(roundPoly …) C_b c0_b c2_b` from the prefix and the row's message).

Reads that return `none`. A row's event charges nothing when its read of
`(P, m)` returns `none`, so the no-hit hypothesis only says something where
the read succeeds. `AspisChecks` must therefore carry the read equalities, as
R1's `Checks` carries `matchingRead`: `aspisRead32 (rs.take 32) = some (d, q)`
(R1's `beforeRho`), `aspisRead33 (rs.take 33) m33 = some (S_W − claimS, S_w −
rhs2)`, and for each round `aspisReadRound (rs.take (34+b)) m_b = some (g_b,
C_b, c0_b, c2_b)`; these are the reads the densities agent left open, and
they must be total on accepted transcripts.

Proof plan: no hit at rows 32–39 gives the four non-membership hypotheses of
`stageCD_sound`; it yields `S_W = claimS` (with `claimDef` this is (P1)),
`S_w = rhs2`, all first-fold residuals zero (so `firstMatch`, through
`pair_queries_match` or directly) and all second-fold residuals zero (so
`residualBatch` trivially, and R1's row-32 event is empty because
`ResidualBatch.bad` of the zero vector is empty). Rows 0–31 are the same
events. Then R1's `checks_noHit_relation` applies to `rs.take 33`, provided
the Aspis protocol's first 33 rounds are R1's protocol's rounds
(`AspisRows40*` must give `(aspisProtocol D).transcript H pub pf 40 |>.rounds.take 33 =
(LiteralByteProtocol.protocol D).transcript H pub pf' 33 |>.rounds` for the
projected proof `pf'`).

Identification lemmas the link needs, stated: (W) the final-sumcheck
model's `∑ f_j W_j` is `RoundPairing.dot row31 (dualFold …)` (unfolding);
(w) `∑ f_j qweight j − rhs2 = −∑ ρ^j residuals j` (from
`secondEncoder_query_eq_natural_sum` and `query_identity`); (sign)
`bad2 iota r0 (−r1) = bad2 iota r0 r1` (roots of a negated polynomial).

### 2.4 Why the order of data and batching challenge is right, and what is not established

At the model level it is right, and this can be read off the definitions:
`firstResiduals d q` and `residuals d q` are functions of `d` and `q`, and
both are read from `P.rounds` (rounds 25–31: the committed words as
transcript messages, γ, α0, α1, the queries) by `LiteralMatchingData.read`;
ρ is the challenge of round 32, drawn after all of them. So the row-32 event
`rhoOf c ∈ pairBad eK d q` is a function of the prefix, exactly as R1's
`LiteralRhoDensity.bad P v` is, and the batched first-fold check is applied
to values fixed before ρ. This is the opposite order to R19's channel fold
(there the combination was taken before the queries and before the data it
combined was pinned), and no extraction from a combination is needed: off
the event every per-query `match0` holds, which is what R1 consumed.

What is not established from what I read: that the Aspis verifier's batched
first-fold equation over the OPENED values equals `firstBatch` over the
COMMITTED words. In the literal model the words are transcript messages; the
link from Merkle-authenticated openings at the queried positions (C1, C2 and
folded trees) to the recorded words is the commitment-recovery layer.
(Correction, from the one-transaction game scoping note: R1's bound reaches
that recovery through `OraclePortFrozenOrder.authenticated`
(OraclePortFrozenOrderSelectedRecovery.lean) via an in-place slot program;
`OraclePortAllSelectedRecoveryC6.authenticated` and
`OraclePortRecoveredAcceptanceC6.accepted_checks`, named here first, are an
earlier draft chain that is in the closure but not used by the bound.) R1
already needs all three trees there, because its per-query `firstMatch`
reads C1, C2 and folded openings; the Aspis counterpart (`accepted ⇒
AspisChecks`) re-uses that recovery but feeds a batched instead of a
per-query equation. Correction: in R1 this whole chain, including the
three-tree recovery, is model-level and inside the closure of
`failure_bound`; only the Rust-to-model join is source refinement. So plan
item 15 is model work (being scoped by the one-transaction game agent,
`AspisOneTx*`), not source refinement.

## 3. File plan, dependency-ordered

Owners: PSA (this agent), PSB (row densities, `AspisRowDensity*`), PSC (pair
binding, `AspisPairResidual*`), PSD (rows 33–39, `AspisRows40*`).

| # | File (module) | Content | Imports from others | Can start now? |
|---|---|---|---|---|
| 1 | AspisRows40Labels (PSD) | labels for n < 40, `row_label` for n < 40 | — | yes |
| 2 | AspisRows40Sampler (PSD) | 40-row sampler delegating rows < 33 to R1's; rows 33–39 plain with `qm31_sample` | 1 | yes |
| 3 | AspisRows40Protocol (PSD) | byte protocol over 2; prefix lemma `take 33 = R1 rounds` | 2 | yes |
| 4 | AspisRows40Decoder (PSD) | decoder: labels < 33 to R1's components, 33–39 to a new parser; raw and adaptive wrappers | 1, 3 | yes |
| 5 | AspisPairResidual (PSC) | `firstResiduals`, `pairBad`, `pairBad_card ≤ 21`, `pair_queries_match` | AspisFinalSumcheckModel | yes |
| 6–7 | AspisRowDensitySampler, AspisRowDensityCaps (PSB) | DONE (cded97cc344): `Sampler.pair_row32_density` (any set of ≤ 21 per prefix, `P.round = 32`), `QM31.combining_mean`/`round_mean` and `Sampler.{combining,round}_unified_density` for rows 33–39 (sets ≤ 1 and ≤ 2, read from `(P, m)`, under `hσ`: rows ≥ 32 use `qm31Sample`), caps `capLambda`, `capRound`, `capPair = rhoCap`, with R1's row-32 statements re-derived | AspisFinalSumcheckModel | done |
| 8 | AspisClassifier (PSA) | `AspisClassifier.bad`, `.budget` (R1's below 32; 6 at 32; 7 at 33–39), density dispatch | 4, 6, 7 | after 4, 6, 7 |
| 9 | AspisRowCharge40 (PSA) | piece (b) for the 40-row decoder (copy of AspisRowCharge with components 33–39) | 4, 8 | after 4, 8 |
| 10 | AspisRowStarts40 (PSA) | piece (c), verifier part, 40 rows; 41 starts | 2, 3, 9 | after 9 |
| 11 | AspisAcceptanceLink (PSA) | `AspisChecks`, `aspis_checks_noHit_r1_checks`, identification lemmas (W), (w), (sign) | 3, 5, 8, AspisFinalSumcheckModel | statements now; proof after 3, 5, 8 |
| 12 | AspisConditionalD3 (PSA) | D3 for the Aspis protocol from 11 and R1's `checks_noHit_relation` | 11 | after 11 |
| 13 | AspisChargedExperiment (PSA) | copies of the recorded/compiled experiment, start-charge prefix and clean event for the 40-row protocol (from the 217 whole-protocol modules, about 117 in the RawCut/RawRecorded/Bin/OraclePort families) | 3, 4, 12 | after 12; the largest item |
| 14 | AspisChargedHitMass40 (PSA) | the composed weighted bound for Aspis | 10, 13 | last in the bound layer |
| 15 | one-transaction game and acceptance (`accepted ⇒ AspisChecks`) | the counterpart of `OraclePortActualAcceptanceC6.accepted_checks` and the one-phase experiment | 13 and the commitment-recovery layer | not scoped here (source/commitment layer) |

Can start before the other agents land: 11 (statements), and the parts of
13 that are pure copies of protocol-generic plumbing once 3 exists.

### 3.1 Changes after the row-densities agent's findings

**Literal layer.** R1's `LiteralTranscript.valid` admits payload rows only
below 33, so R1's literal transcript cannot hold rows 33–39. Choice: a new
literal-transcript layer (`AspisLiteral40`: `valid40 n m := if n < 33 then
LiteralTranscript.valid n m else` the row's typed payload decodes; the
message type and the restore/enrichment maps extended for rows 33–39), not a
route that stays at the unified-sampler level. Reason: everything that
consumes the classifier on the R1 side (the classifier itself,
`LiteralDecoderEnrichment.density`, `RawLiteralDecoderDensity`, the matching
reads, `checks_noHit_relation`) is at the literal level, and the link of
section 2 uses R1's literal `Checks` on `rs.take 33`. Staying at the unified
level would mean restating that consumer chain. Cost: 2–3 more files (the
literal transcript and byte sampler for 40 rows, and the enrichment/restore
extension), placed between items 3 and 4; the row-33–39 densities stated at
the unified-sampler level by PSB feed it through a 40-row copy of
`LiteralDecoderEnrichment.density`, under PSB's `hσ` (the 40-row sampler must
reuse `UnifiedSampler.samp` for those rows and draw with `qm31Sample`, which
R1's challenge map already does for every row ≥ 32: `selected_sigma_rho`).

**From fresh-answer densities to the shared oracle.** R1 has this transport
for row 32, and it is generic in the bound and the observable but specific to
each decoder component: the fixed-round independent-answer bound
(`hfixed`) is turned into a background-law bound of a decoded start by the
component law (`JointUnifiedBound.decoded_bound` for row 32;
`UnifiedSemanticLaw`, `UnifiedOpeningLaw`, … for the others), then into the
shared-oracle hit mass by the decoded first-read union bound, which in the
per-step form is piece (a) and is generic. So rows 33–39 need one new
component law (a copy of `JointUnifiedBound` over the new parser of item 4),
after which (a) and the class dispatcher (copy of `AspisRowCharge`) apply
unchanged in form.

Revised count for the bound layer of the 40-row instance, excluding the
charged-experiment copies (item 13) and the source/commitment layer (item 15):
about 15–20 files across PSA and PSD, plus PSB's done and PSC's in progress.


## 4. Item 11 status (acceptance-to-extraction link): COMPILED

Files: `lean/AspisAcceptanceAlgebra.lean` (generic algebra),
`lean/AspisAcceptanceLink.lean` (the link on R1's literal carrier),
`lean/AspisAcceptanceLinkR40.lean` (on the Aspis 40-row protocol). All
model theorems; no hypothesis about another agent's piece is left:

- the pair-binding piece is used directly (`AspisPairResidual.firstResiduals`,
  `pairBad`, `firstResidual_eq_zero_iff`, `Row32.bad`); its shapes match what
  section 2.3 asked for (`pair_all_zero` has exactly the shape written there
  as `pair_queries_match`; the agent's `pair_queries_match` concludes the
  matching-set membership instead, and the link does not need it because
  `stageCD_sound` already gives both residual families zero);
- the prefix lemma is `AspisRows40.Literal.transcript_take33`, which matches
  the hypothesis `hprefix` of `aspis_relation_of_checks` exactly (second
  conjunct, `n := 40`).

Theorems: `link_model` (generic, AspisAcceptanceAlgebra), `not_pair32`,
`not_lam33`, `not_rounds`, `r1_noHit33`, `checks_of`,
`aspis_checks_noHit_r1_checks` (R1's `Checks` and R1's no-hit on `rs.take 33`),
`aspis_relation_of_checks` (with `hprefix`, then R1's
`checks_noHit_relation`), `aspis_relation` (with `transcript_take33`).

Parameter, not a hypothesis: `decodePair : LiteralTranscript.Message →
Option (WideExact × WideExact)`, the codec of the 64-byte payload of rows 33
to 39 into two field values; it must be the verifier's canonical decoding
(an obligation of the acceptance layer).

Design point learned: concrete statements must be instances of generic
definitions (`FirstBatch`, `FinalCheck`, `lamBadSet`, `roundBadSet`, as R1's
`HchecksAccumulator` does); re-elaborating field arithmetic over the concrete
tower and passing it to a generic theorem made the elaborator unfold the
tower's field instance and time out (attempts PSA-d-04 to d-11, kept below).

Receipts (build host, L187 objects, `fv_lean.sh`):

| Attempt | Module | sha256 | Exit | Wall | RSS (time) | cgroup |
|---|---|---|---|---|---|---|
| PSA-d-12 | AspisAcceptanceAlgebra | 47ffafbb…856b97 | 0 | 3.43 s | 3,096,104 KB | — |
| PSA-d-13 | AspisAcceptanceLink | 55b14b95…a256c2 | 0 | 20.39 s | 3,597,800 KB | 421,588,992 |
| PSA-d-14 | AspisAcceptanceLinkR40 | 67dc5e5d…2311 | 0 | 1.65 s | 3,559,140 KB | 366,399,488 |

All axiom lines `[propext, Classical.choice, Quot.sound]`. Failed attempts:
PSA-d-01/02 (sign lemma: decidability instances in a filter), d-04 to d-11
(unknown lemma names; a `simp` past R1's classifier; the instance timeouts
above, localised by splitting the proof into lemmas). Two scratch probes
(PSA-probe-01/02, `AspisProbeInst*`, not results) printed instance arguments.

Plan changes taken from the other agents' notes:

- item 9 (piece (b) for 40 rows): R1 frames through `decAspis_of_r1` and the
  existing `AspisRowCharge` result; frames of rows 33 to 39 through
  `AspisRows40Final.component_bound` with the bad sets supplied by
  `lamBadSet` and `roundBadSet` above (row 33 size ≤ 1, rows 34 to 39 ≤ 2);
  the charge for rows 33 to 39 must use the new public selection
  `FinalByte.select n` (walk back to row 32);
- item 10 (piece (c), 40 rows): combine `AspisRows40.Starts` with
  `AspisRowStarts`; the weighted count needs only upper bounds, so "exactly
  one start per new row in an honest run" is not needed; the reseed frame
  (row 26) parses as a frame of any row 0 to 39 for some state values and is
  charged the largest cap over all 40 rows.
