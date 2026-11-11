# The Aspis model-level failure bound: end-to-end assembly with named gaps

Status, 2026-11-11. "R1" is the two-transaction verifier and its Lean
development (the L187 closure, read from the flat copy of its sources).
"Aspis" is the one-transaction verifier (`verify_summed_format`, 40-row
transcript) and its model in this directory. No figure in this note is
established. Every number below is conditional on the open hypotheses in the
first table. The release target is unchanged and not yet established. R1's
claim is not restated or tightened.

## 0. What is open (the hypotheses of the assembled theorem)

The assembled theorem is `AspisFailureBound.failure_bound40P`
(lean/AspisFailureBound.lean, compiled PSA-f-07). Its only hypotheses besides
R1's query bound `hq` are these three propositions. Each is stated on the run
`eval H (expE D P)` of the Aspis full experiment at the one-transaction
decision (`expE D P := AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P`,
typed as R1's `Experiment`). `rounds40 D H run` is the 40-row transcript
`((AspisRows40.Protocol.protocol D).transcript H run.2.1.1 run.2.1.2 40).rounds`.
Every hypothesis assumes `accepted` (`run.2.2 = true`) and
`no collision` (`¬ RecordedBinaryExperimentBin.binaryCollision (Q+1111) run`).

| Name | Exact type (after `∀ H, accepted → no collision →`) | R1 theorem it copies | Owner (proposed) | Size estimate | Copy or new |
|---|---|---|---|---|---|
| `AcceptedChecks40 D P Q` | `Nonempty (AspisAcceptance.AspisChecks AspisOneTx.decodePairS run.2.1.1 (rounds40 D H run))` | `Frozen2StartChargeClean.accepted_facts`, first conjunct, through `OraclePortFrozen2Consumer.fibre_checks` ← `OraclePortFrozen2C6.checked_acceptance` ← `OraclePortFrozen2CanonicalChecks.accepted_checks` ← `OraclePortFrozen2ActualChecks.accepted_checks` ← `OraclePortFrozenOrderChecks.accepted_checks` | one-transaction game agent (its item M7; the last link, `accepted_checks_aspis`, is compiled) | 4 to 6 copied modules above `accepted_checks_aspis`, plus M7 | mostly copy. M7 is new content: the containing log, frames and root reads identified with the 40-row run. It needs the 40-row oracle-decision experiment. |
| `WordAlignment40 D P Q` | `RawCutTranscriptRun.proof (RawCutWordsFromRunExecutableBin.wordsFromRun run) run.2.1.2 = run.2.1.2` | `OraclePortCleanModel.extractor_word_alignment` (second conjunct of `accepted_facts`) | rows agent (PSD), whose `wordsFromRun` delegation lemmas cover rows 0, 2, 30 | 1 to 2 modules | copy. The words come from rows 0, 2 and 30, which are R1's rows in the 40-row protocol (`Protocol.chain_eq`). R1's proof takes R1's 33-row checks and must be restated for the 40-row run. |
| `HitInPrefix40 D P Q` | `GenericNoHit.hitFrom (AspisAcceptance.bad AspisOneTx.decodePairS) run.2.1.1 [] (rounds40 D H run) → AspisRec40.HitMass.prefixHit (classifier40 AspisOneTx.decodePairS) D P run` | `Frozen2StartChargeCompletion.{decodes, hit_in_prefix}`, `RWireCheckedFormat.{format_of_checks, format_of_enrich}`, `Frozen2StartChargePrefix.{same_transcript, chronological_prefix}`, `OraclePortAdmission.accepted_tag` | rows agent (PSD) (`decFinal`, `AspisRec40.*`) | 3 to 5 modules | rows 0 to 32 are a copy: R1's decoder is a component of `decFinal`. Rows 33 to 39 are new: completeness of the byte decoder `FinalByte.fin`, meaning every row-33-to-39 frame of an accepted run is decoded as a start in the charged trace. |

How the estimates were made. The constant-dependency closures of the R1
roots were measured with the rows agent's method (`lean/AspisFailureMeasure.lean`,
PSA-f-01, measurement only, no theorems). The walk expands only through modules
that depend on a replaced definition or are two-transaction (the rows agent's
`measure-expand.txt`). Every other module is a leaf and is reused unchanged.

| Root group | R1 roots | Changed-dependent modules reached | Two-transaction (class iii) |
|---|---|---:|---:|
| gap 1, checks | `OraclePortFrozen2Consumer.fibre_checks` | 106 | 14 |
| gap 1, tag | `OraclePortAdmission.accepted_tag`, `OraclePortFrozen2Consumer.admitted_dV` | 49 | 10 |
| gap 2, words | `OraclePortCleanModel.extractor_word_alignment` | 48 | 0 |
| gap 3, hit in prefix | the six roots in the table above | 199 | 10 |
| abort (reused) | `shared_oracle_failure_le_hit_add_abort`, `…_supplied_hit_bound`, `CleanAcceptedModel`, `failureMass` | 63 | 0 |
| query scan (reused) | `QueryScanModelFailure.{exhaustion_bound, failureProbability}` | 0 | 0 |
| collision (reused) | `BinCombinedMerkleCollision.{mass, kappa}` | 0 | 0 |
| all groups | | 273 | 14 |

Reaching a module is not the same as needing a copy of it.
- Gap 3 reaches 115 modules that gap 1, gap 2 and the abort group do not. They
  are almost all R1's unified decoder, public selection and table-word modules.
  The rows agent found these reused unchanged as components of `decFinal`
  (RECORDED-EXPERIMENT-40.md §1.1). The 10 two-transaction modules gap 3 reaches
  are shared with gap 1, through `recovered` and the decision.
- The two-transaction modules sit only in gap 1:
  `OraclePortFrozen2{Decision, Bounds, Checkpoint, Trace}`,
  `OraclePortCheckpoint*C5`, `OraclePortCheckpointStateC3`,
  `OraclePortAcceptedContextC6`, `R16Decision{Checkpoint, QueryModel}` and
  `R1VerifierCallBudget`. The one-transaction agent's `AspisOneTx*` files
  already replace the decision, its budget, the merged slots and the frozen-order
  checks.
- The abort group reaches 63 modules and needs no copy. The assembled theorem
  applies R1's abort theorem as it stands: its premise is about R1's 33-row
  transcript, which the Aspis transcript's first 33 rows equal
  (`transcript_take33`).

The sizes in the first table are estimates from these lists and from the
copies already made. They are not counts of written files.

## 1. R1's assembly, quoted

### 1.1 From the restricted union bound to `failure_bound`

R1 has two parallel chains with the same shape: the stored chain
`Frozen2StartChargeProbability` and the F3T chain `F3T_Probability`. The
headline goes through F3T. Both are quoted from the L187 sources.

```lean
-- Frozen2StartChargeProbability.lean:29 (F3T_Probability.lean:31 the same with canon P)
theorem restricted_union_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    lazyMean (projected D P) emptyTable (fun run => indicator (prefixHit D P run)) ≤
      ((Q+34 : Nat) : ℚ)*PerAttemptEnvelope.B

-- Frozen2StartChargeProbability.lean:40 (F3T_Probability.lean:42)
theorem failure_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    lazyMean (projected D P) emptyTable failureMass ≤
      BinCombinedMerkleCollision.kappa (Q+1161) +
        ((Q+34 : Nat) : ℚ)*PerAttemptEnvelope.B + 1/(2:ℚ)^126
```

`failureMass run` is the mean over the extractor's private coins of
`run.2.2 = true ∧ RawRecordedPublicSpendExtractorBin.extract run coins = none`
(RawRecordedOracleExtractionMassBin.lean:44). In words: accepted, and R1's
extractor returns no witness.

The proof of `failure_bound` has three steps:
1. `hc := BinCombinedMerkleCollision.mass iv (Q+1161) (projected D P)
   (OraclePortFrozen2Probability.first_reads D P Q hq)`.
2. `hs := restricted_union_bound`.
3. `shared_oracle_failure_le_supplied_hit_bound D (projected D P) (bad D P Q)
   (clean D P Q hq)` with `bad := binaryCollision (Q+1161) ∨ prefixHit`. The
   bad mass is bounded by `hc + hs` through `indicator_or_le` and `lazyMean_add`.

### 1.2 Each term and what supplies it

| Term | Value in R1 | Supplied by | Protocol-level or account-only |
|---|---|---|---|
| start | `(Q+34)·B` | `restricted_union_bound` ← `RawAdaptiveClassifierStartBound.shared_hit_mass_le_starts` with `Frozen2StartChargePrefix.starts` (≤ Q+34) | protocol-level (Fiat-Shamir challenges in the random-oracle model) |
| collision | `kappa(Q+1161) = 6(Q+1161)²/2^256` | `BinCombinedMerkleCollision.mass` (generic in the program) at `OraclePortFrozen2Probability.first_reads` (≤ Q+1161; 1,161 = sampler 115 + slots 477 + 563 + checkpoint 6) | protocol-level (binding of the Merkle commitments in the model verifier's log). The checkpoint 6 is two-transaction. |
| clean event | accepted ∧ ¬collision ∧ ¬prefixHit ⇒ checks and no hit on the 33-row transcript at the re-enriched proof (`CleanAcceptedModel`) | `Frozen2StartChargeClean.clean`, from `accepted_facts` (checks, word alignment, tag), `RWireCheckedFormat.format_of_checks/enrich`, `chronological_prefix`, `first_reads`, `Frozen2StartChargeCompletion.decodes` and `hit_in_prefix` | protocol-level (model verifier acceptance ⇒ checks ⇒ extraction) |
| abort | `2^-126` | `shared_oracle_failure_le_hit_add_abort`: on a clean accepted run, `extract_of_checks_noHit_bank` gives a witness unless the GS byte bank fails, and `LiteralFreshBankAbortComposition.bankAbortMass_le` bounds that failure by `2^-126` uniformly in the inputs | protocol-level (property of the extractor) |
| query scan | `2^-454` | not in `failure_bound`. It is added one layer up: `F3T_RuntimeBound.failureModel runtime := deployedFailure runtime + QueryScanModelFailure.failureProbability (2^18)`, bounded by `QueryScanModelFailure.exhaustion_bound` | protocol-level (the 64-word scan that derives 22 distinct query positions; a property of the verifier's sampler, not of the chain). R1 attaches it at the runtime layer. |
| account | `accountLoss Q = 6(Q+2965)²/2^256` | not in `failure_bound` or `failureModel`. It is the mass of the account-run collision event `E_rec` on the adversary's own two-phase account run (`F3T_AccountCharge.bound`, reads ≤ Q+2965 = 1921+1040+4) | **account-only**: it exists because the headline's outcome conjunct is evaluated on the on-chain account run, not on the model log |

### 1.3 From `failure_bound` to `RPz7_F3T_Numeric.total`

```lean
-- RPz7_F3T_RuntimeBound.lean
def failureModel (runtime : Runtime) : Rat :=
  deployedFailure runtime+QueryScanModelFailure.failureProbability (2^18)

theorem failure_bound {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : Physical rust)
    (raw : AcceptedVerifierJoin c D rust) (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q) (runtime : Runtime)
    (binding : StoredCarrierBinding c D rust P runtime) :
    failureModel runtime≤StartChargeNumeric.totalBound Q
-- StartChargeNumeric.totalBound Q = envelope Q 34 1161
--   = (Q+34)·B + kappa(Q+1161) + 2^-126 + 2^-454

-- RPz7_F3T_Numeric.lean
def accountLoss (Q : Nat) : Rat := 6*((Q+2965 : Nat) : Rat)^2/(2:Rat)^256
def collisionLoss (Q : Nat) : Rat := 6*((Q+1161 : Nat) : Rat)^2/(2:Rat)^256
def total (Q : Nat) : Rat :=
  ((Q+34 : Nat) : Rat)*PerAttemptEnvelope.B + collisionLoss Q + accountLoss Q +
    1/(2:Rat)^126 + 1/(2:Rat)^454
```

The step from `failure_bound` (F3T) to `failureModel`:
- `F3T_Runtime.transport` gives `deployedFailure runtime ≤` the model failure
  mass. It does so under the source-refinement hypotheses `physical`,
  `raw : AcceptedVerifierJoin` and `binding : StoredCarrierBinding`.
- `exhaustion_bound` adds the scan term.

The step to `total`: the headline (`NDO_Rc7_Top`, `NNH8_Top`, `NHZ_SameLaw`)
concludes `failureModel runtime ≤ F3T_Numeric.total (Q0+Q1)` next to the
outcome conjunct. EVB_EventB.lean §4 describes how the account term is charged:
- per world, the deployed loss is `max r (indicator ¬Outcome)`;
- `r ≤ m + e` holds, where `e` is the indicator of `E_rec`;
- `¬Outcome ⇒ E_rec` holds by `top_splitB`;
- the mean of `e` is at most `accountLoss` (`F3T_AccountCharge.bound`).

So `E_rec` is charged once. The same file notes that the averaging step for
`max r _` "is a host restatement … not compiled here". I record that remark and
do not re-check it.

## 2. The Aspis counterparts, stated

Game: the one-phase game of ONE-TRANSACTION-GAME.md §1.2, with the owner's
decisions:
- D1: one phase, with the same adversary class, work metric, averaging and
  failure event.
- D2: the split-B failure event with an account term.
- D3: R1's normalisation rule.

The owner has also put the Pool's payout inside the game for Aspis (§1.2a,
form (B), `PayoutBound`). That adds a conjunct to the outcome, so it enlarges
the failure event. **It is not part of either bound below.** Neither statement
mentions it. It is an open obligation of the game-level theorem (§9.3 of that
note).

### (P) Protocol-level bound: no account term

For the 40-row one-phase model experiment with decision `dV_aspis`, classifier
`classifier40 decodePairS`, R1's failure observable and R1's extractor, for
every adversary `P` with `∀ H, (eval H P).1.length ≤ Q`:

```
E_H[failureMass(run_H)] + scanFailure ≤ kappa(Q+1111) + (Q·capMax + verifierCharge40) + 2^-126 + 2^-454
```

`scanFailure = QueryScanModelFailure.failureProbability (2^18)`. This is the
form compiled in §3, conditional on the three hypotheses of §0.

Compared with R1's `totalBound Q = (Q+34)·B + kappa(Q+1161) + 2^-126 + 2^-454`:
- the collision envelope 1,161 becomes 1,111. That count is the rows agent's
  `projected_first_reads` at `dV_aspis`: 136 transcript calls and 975 merged
  slots, with no checkpoint;
- the uniform start term becomes the per-step term (owner decision, Aspis
  only);
- the abort and scan terms are R1's.

(P) has no runtime or source hypotheses. It is a statement about the model
experiment, not the deployed program.

### (G) Game-level bound: with the account term

With `r_H` the deployed per-world loss of the Aspis entry (the Aspis copy of
`F3T_Runtime.runtimeMass` plus the scan term) and `Outcome1` the Aspis copy of
R1's outcome:

```
E_H[max(r_H, ind(Runs1 ∧ ¬Outcome1))] ≤ (P) + accountLoss40(Q),
accountLoss40(Q) = 6(Q + A)²/2^256
```

`A` is the Aspis account run's read budget. It has no derivation.
ONE-TRANSACTION-GAME.md §2.3 gives a paper count of 2,086 at the head (1,111
wrapper and 975 replay, with no audit reads), and the proved count waits for an
extracted Aspis entry. (G) also needs Aspis copies of `F3T_Runtime.transport`
and its source hypotheses, plus the `E_rec` charging argument. None of these
exists.

**Only (G) corresponds to R1's headline** (`failureModel ≤ total`, next to the
outcome conjunct). (P) corresponds to R1's `totalBound`, which R1 never
advertises alone. Even (G) leaves out `PayoutBound`. With `PayoutBound` the
failure event is strictly larger than R1's, which is the owner's form (B).

## 3. The assembly in Lean (COMPILED, conditional)

File `lean/AspisFailureBound.lean`, namespace `AspisFailureBound`, attempt
PSA-f-07. The axioms are `[propext, Classical.choice, Quot.sound]` for every
theorem.

```lean
theorem failure_bound40P (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (g1 : AcceptedChecks40 D P Q) (g2 : WordAlignment40 D P Q) (g3 : HitInPrefix40 D P Q) :
    lazyMean (exp D P) emptyTable failureMass + QueryScanModelFailure.failureProbability (2^18) ≤
      BinCombinedMerkleCollision.kappa (Q+1111) +
        ((Q : ℚ) * capMax + verifierCharge40) + 1/(2:ℚ)^126 + 1/(2:ℚ)^454
```

Here `exp D P = AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P`. Also in
the file:
- `failure_bound40` is the same bound without the scan term: R1's
  `failure_bound` shape.
- `clean40` gives `CleanAcceptedModel D (expE D P) (bad40 D P Q)` from
  `g1`, `g2` and `g3`.
- `clean_core` is the step at one run.
- `bad40 := binaryCollision (Q+1111) ∨ prefixHit (classifier40 decodePairS)`.

What each piece is and where it comes from:

| Piece | Status | Source |
|---|---|---|
| start term `Q·capMax + verifierCharge40` | proved | `AspisPerStep.ChargedHitMass40.restricted_union_bound_weighted40` (PSA-e-14), at `d := dV_aspis`, `decodePair := decodePairS` |
| collision term `kappa(Q+1111)` | proved | R1's `BinCombinedMerkleCollision.mass`. It is generic (any `Program Bytes State O` with a first-read budget) and is instantiated here at the rows agent's `AspisRec40.CallBudgetAspis.projected_first_reads` (≤ Q+1111) |
| step from Aspis checks and no Aspis hit to R1's checks and R1's no-hit on the first 33 rows | proved | `AspisAcceptance.aspis_checks_noHit_r1_checks` (item 11) with the rows agent's `AspisRows40.Literal.transcript_take33`, in `clean_core` |
| abort `2^-126` | proved, R1's theorem unchanged | `RawRecordedOracleExtractionMassBin.shared_oracle_failure_le_supplied_hit_bound` (with `shared_oracle_failure_le_hit_add_abort` and `bankAbortMass_le` inside). It applies to the first 33 rounds unchanged through `transcript_take33`, because its premise `CleanAcceptedModel` speaks of R1's 33-row transcript at the re-enriched proof and `clean40` supplies exactly that. No 40-row copy is needed. The extractor is R1's, and the relation is R1's `LiteralProtocol.relation`. |
| query scan `2^-454` | proved, R1's theorem unchanged | `QueryScanModelFailure.exhaustion_bound`. It is a constant and does not depend on the run. Its relevance to Aspis rests on the row-31 query derivation being R1's (rows 0 to 32 are R1's rows). Its link to the deployed sampler is the runtime layer (G), as in R1. |
| clean event | three open hypotheses | §0 |
| account term | absent from (P) | (G), not assembled |
| payout conjunct | absent from (P) and (G) | ONE-TRANSACTION-GAME.md §1.2a, §9.3 |

Checks on the hypotheses (AGENTS.md §3):
- **They do not contain the conclusion.** None mentions `failureMass`, the
  extractor, a probability or a bound. Each is a pointwise fact about a single
  run and has the same form as an R1 lemma that R1 proves.
- **They are satisfiable.** If no run is accepted, all three hold vacuously and
  the bound holds trivially, since `failureMass` is 0. They have content
  exactly where R1's counterparts do.
- **Quantifiers.** The quantifiers match R1's: for all `H`, on the run of the
  fixed adversary `P`.
- **`decodePairS`** is the one-transaction agent's codec for rows 33 to 39.
  The bound is stated at that codec, which is the one its acceptance chain
  produces `AspisChecks` for.

Not covered:
- the relation and the withdrawal destination (the PIN2 conjunct question in
  V8-LESSONS-CHECK.md, finding 3; `PayoutBound`);
- the source refinement of `dV_aspis` and the Aspis entry;
- campaign accounting (D4);
- anything about the deployed program.

## 4. Arithmetic of (P), conditional on the three hypotheses

This is exact rational arithmetic (Python `fractions`) from the compiled
definitions, with `capMax` and `verifierCharge40` as in PER-STEP-ACCOUNTING.md
§3.1, `kappa(n) = 6n²/2^256`, and `B = 15/2^109` for comparison. It follows
only from `failure_bound40P` **and** the three open hypotheses. It is not
established.

At Q = 0, (P) is `kappa(1111) + verifierCharge40 + 2^-126 + 2^-454`:

| Term | Value |
|---|---|
| `verifierCharge40` | 0.150672·2^-100 |
| `kappa(1111)` | 2^-233.18 |
| abort | 2^-126 |
| scan | 2^-454 |
| **(P) at Q = 0** | **0.150672·2^-100 = 2^-102.7305** (< 2^-100 as rationals; margin 0.849328·2^-100) |

For comparison only, R1's `total(0)`, which includes R1's account term, is
0.996094·2^-100. The two numbers are not like for like. R1's is the
game-level figure under R1's own, partly open, obligations. This one is (P),
model-level and conditional.

Valid range in the form of R1's corollary, `(P)(Q) ≤ (Q+1)·2^-100`:
- `(P)(Q) − (Q+1)·2^-100` is a convex quadratic in Q and is negative at Q = 0,
  so the set where the inequality holds is an interval;
- by exact bisection, it holds for **0 ≤ Q ≤ 14,792,851,739,245,801,786,899,753,358,511,503,419,343,343,973 ≈ 2^153.37**
  and fails at the next integer;
- the upper end is set by the collision term.

Illustration only, not a result: with an account term `6(Q+A)²/2^256`, the
value at Q = 0 does not change at 6 significant figures for any `A` up to
10^5. With `A = 2965` (R1's number, not justified for Aspis), the range would
end near 7.40·10^45 ≈ 2^152.37.

## 5. Validation

All compiles ran on the build host against the L187 objects with
`fv_lean.sh` (MemoryHigh 6G, MemoryMax 8G, no swap). "RSS (time)" includes
the memory-mapped objects. "cgroup" is the scope's `memory.peak`.

| Attempt | Module | sha256 | Exit | Wall | RSS (time) | cgroup | Note |
|---|---|---|---|---|---|---|---|
| PSA-f-01 | AspisFailureMeasure (measurement only) | 304e57d8…5e32 | 0 | 3.91 s | 4,224,068 KB | 428,339,200 | writes `psa-failure-measure.tsv` on the host |
| PSA-f-02 | AspisFailureBound | a03fb590…d01c | 1 | 58.23 s | 4,216,272 KB | 432,734,208 | heartbeat timeout in `clean40` |
| PSA-f-03 | AspisFailureBound | 36adb33a…d3a5c | 1 | 48.36 s | 4,215,104 KB | 430,219,264 | extractor argument of `transcript_take33` not inferable; timeout in `clean40` |
| PSA-f-04 | AspisFailureBound | 9b0035e1…66b8 | 1 | 52.04 s | 4,214,412 KB | 427,749,376 | `clean_core` compiled; timeout in `clean40` |
| PSA-f-05 | AspisFailureBound | c0491764…64b9 | 1 | 47.34 s | 4,211,940 KB | 420,773,888 | timeout in `clean40_at` |
| PSA-f-06 | AspisFailureBound | 58f13526…3e11 | 1 | 52.01 s | 4,211,252 KB | 420,171,776 | same, after stating the hypotheses at R1's `Experiment` carrier types |
| PSA-f-07 | AspisFailureBound | 32c18c4f…16be | 0 | 4.65 s | 4,228,340 KB | 426,835,968 | 5 axiom lines, all standard |

Scratch probes PSA-probe-03 to 07 (`AspisFailureProbe`, not a result, not
committed) located the timeout. It was the defeq check between a
`GenericNoHit.hitFrom` hypothesis and its use. Two causes:
- the run carried R1's `RawCutProverCompiler` carrier types in one place and
  `LiteralTranscript` types in the other (fixed by `expE`, typed as R1's
  `Experiment`);
- `hitFrom` and `hitsChain3` were unfoldable. R1 marks `R0C.V3.hitsChain3`,
  `GenericNoHit.hitFrom` and `LiteralClassifier.bad` `local irreducible` in
  the same position, and the fix copies that line, adding `AspisAcceptance.bad`.

No heartbeat limit was raised, and no attempt came near the memory cap.

## 6. Next deliverables

In order of what they unblock:
1. `HitInPrefix40` and `WordAlignment40` (rows agent). Both are copies, apart
   from the completeness of the rows-33-to-39 byte decoder.
2. `AcceptedChecks40` (one-transaction agent). This is the copies above
   `accepted_checks_aspis` plus M7.
3. Then (P) holds without hypotheses beyond `hq`, as a model theorem.
4. (G) needs, in addition:
   - the extracted Aspis entry;
   - the Aspis transport and its source hypotheses;
   - the account budget `A`;
   - the `E_rec` charge;
   - `PayoutBound` for the owner's form (B).

## 7. Joined: form (P) with one open hypothesis (lead, 2026-11-11)

**CORRECTION, same day (soundness lead's reviewer, on ef4cd439a53): the open
hypothesis below is mis-stated, and this section's theorem is vacuous for some
provers.** `FinalDecoding40` asks rows 33 to 39 to decode on every run that
meets R1's four premises. None of those premises says anything about rows 33
to 39: R1's `Format` makes R1's 33 rows valid and nothing does that for the
late rows. The reviewer's counterexample, from the source: a prover with
statement tag 2, rows 0 to 32 in `Format`, and `.initial` at rows 35 and 36.
Canonicalisation and enrichment keep `.initial`; on `.initial` past row 0 the
sampler returns the squeeze of the initial cell, so rows 35 and 36 have the
same first cell and the same table before it; `FinalDecodes` would then make
the 35-round and the 36-round transcripts equal, which is impossible; and all
four premises can hold. For such a prover `FinalDecoding40 D P Q` is false and
`failure_bound40P_of_final` says nothing.

What was wrong on my side: I read the statement and did not test whether its
hypothesis can hold. It is the same kind of error as the first form of the
payout theorem (ONE-TRANSACTION-GAME.md section 11), found the same day.

The repair is known and does not weaken the bound: the hit-in-prefix step is
only needed on accepted runs, and there the `AspisChecks` value constrains the
late rows (payload, the 64-byte frame, canonical decoding, the certificate
tie). The hypothesis is being restated with that premise, supplied from the
checks inside `hit_in_prefix_of`, with the counterexample retained and a
satisfiability check added. Until the restated files are compiled, read this
section as: form (P) is conditional on a hypothesis that is NOT YET CORRECTLY
STATED. The composition itself (which hypotheses the bound takes, the terms on
the right) was confirmed by the reviewer.

Other points of the same review, recorded:
- The lift from the fixed-proof statement is sound pointwise in the oracle.
  It is not "without C7": `fibre_checks40` is stated at C7's `pairProver` and
  that module is in the constant walk; only R1's `annotated_selected` is
  unused.
- The tag step does use the Aspis admission (through `admitted_aspis` and
  `accepted_guardS`), keeping only the tag conjunct. No validity of rows 33 to
  39 is used anywhere, which is why the hypothesis had nothing to stand on.
- The right-hand side is `kappa(Q+1111)` plus the weighted start charge plus
  `2^-126` (plus `2^-454` in form (P)); no account term, no payout conjunct,
  no campaign accounting, no figure.
- The constant walk can miss constants that occur only in the field types of
  a structure whose constructor is never used. The walk was extended to visit
  constructors (see the table below).
- Stale headers in `AspisRec40CleanWords` and `AspisRec40CleanTag`, to be
  corrected at the coherent rebuild.

The text below is the section as first written.

The three hypotheses of section 0 are now reduced to one.

`AspisRec40.CleanJoin` (the clean-event work, RECORDED-EXPERIMENT-40.md section 8) proves the
assembly's definitions as stated:
- `accepted_checks40 : AcceptedChecks40 D P Q`, from the query hypothesis `hq` alone. It uses
  `AspisOneTx.Checked.fibre_checks40` through R1's `fibre_prover` and the 40-row selection step
  `CleanA.projected_eq_recorded`.
- `word_alignment40 : WordAlignment40 D P Q`, from `hq` alone.
- `hit_in_prefix40 : HitInPrefix40 D P Q`, from `hq` and one further premise, `hfinal`.

`lean/AspisFailureBoundJoined.lean` composes them with `failure_bound40P`:

```lean
def FinalDecoding40 (D) (P : Prover) (Q : Nat) : Prop :=
  ∀ H : Bytes → State,
    firstReads emptyTable (eval H (AspisRec40.ChargePrefix.base D P)).1 ≤ Q+1111 →
    ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
        BinRawByteCollisionTargets.pred (Q+1111)) emptyTable
        (eval H (AspisRec40.ChargePrefix.base D P)).1 →
    RWireCheckedFormat.Format (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 →
    (eval H (AspisRec40.ChargePrefix.base D P)).2.1.1.tag = 2 →
    AspisRec40.CleanStatement.FinalDecodes D H (eval H (AspisRec40.ChargePrefix.charged D P))

theorem failure_bound40P_of_final (D) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (hfinal : FinalDecoding40 D P Q) :
    lazyMean (AspisFailureBound.exp D P) emptyTable failureMass +
        QueryScanModelFailure.failureProbability (2^18) ≤
      BinCombinedMerkleCollision.kappa (Q+1111) +
        ((Q : ℚ) * capMax + verifierCharge40) + 1/(2:ℚ)^126 + 1/(2:ℚ)^454
```

What the remaining hypothesis says: on the charged run of the 40-row experiment, under R1's four
premises (first reads at most `Q + 1111`, no collision event, the wire format, statement tag 2),
the Aspis decoder recovers rows 33 to 39 (`FinalDecodes`: for each of those rows, the decoder
returns at the row's first cell and following it gives the row's transcript prefix, message and
challenge). It is a statement about the model. It is to be proved, not assumed; the clean-event
work estimates 10 to 15 modules (RECORDED-EXPERIMENT-40.md section 8.2). Per the reviewer's
caveat it cannot come from admission and has to come from the shapes of rows 33 to 39.

Status of form (P): a conditional model theorem with one open hypothesis. Still no figure. The
arithmetic of section 4 stays conditional. Form (G) is unchanged: it needs the account term and
the source side.

**No two-transaction module is used.** The clean-event work's audit found one constant from a
class iii module in this closure: `R1VerifierCallBudget.firstReads_le_length`, used at
`AspisOneTxRun.lean:107`. It is a generic fact (first reads are at most the trace length) and the
rows work had already re-proved it as `AspisRec40.CallBudget.firstReads_le_length`. Line 107 now
uses the re-proved lemma; nothing else in the file changed. `AspisOneTxRun` and the three modules
above it were recompiled. A constant walk rooted at `failure_bound40P_of_final`
(`lean/AspisJoinedMeasure.lean`, every non-library constant expanded, proof terms included)
reaches 1,003 project modules and 11,894 project constants, and no class iii module. Its import
closure holds 32 class iii modules; none of their constants is used. Module list:
`joined-measure.tsv`.

| Attempt | Module | Source sha256 | Exit | Wall | Peak RSS (time) | cgroup peak | Axioms |
|---|---|---|---|---|---|---|---|
| LDJ-01 | AspisFailureBoundJoined | 05a140378b1c3f9f4537cd67c89b4788628a4c635824c4a4abe18b3b266a6506 | 0 | 2.30 s | 4,248,176 KB | 419,840,000 B | [propext, Classical.choice, Quot.sound] |
| LDJ-02 | AspisOneTxRun (line 107 changed) | 26cbb3f61f10a5f6a4c14aae485cb90549c482013947d8b5c03591c03d60ec97 | 0 | 3.26 s | 4,271,316 KB | 444,780,544 B | standard three |
| LDJ-03 | AspisOneTxCheckedAcceptance (source unchanged, recompiled) | cf5d5b2c22d7f49ba6ee02e6a802effffcf54e74ea6929f3fa7f4a220297383b | 0 | 3.01 s | 4,254,480 KB | 429,285,376 B | standard three |
| LDJ-04 | AspisRec40CleanJoin (source unchanged, recompiled) | 695c79cc89487a90f1b1eef54f19acaa4eaefebc25fde422904ac85a910e8041 | 0 | 2.41 s | 4,249,268 KB | 420,229,120 B | standard three |
| LDJ-05 | AspisFailureBoundJoined (source unchanged, recompiled) | 05a140378b1c3f9f4537cd67c89b4788628a4c635824c4a4abe18b3b266a6506 | 0 | 2.28 s | 4,253,492 KB | 424,812,544 B | [propext, Classical.choice, Quot.sound] |
| LDM-03 | AspisJoinedMeasure (measurement only) | 1a626725f12551af75df4f87e7662c42801f3789c086b2209521ea7e9c352ac9 | 0 | 9.00 s | 4,317,316 KB | 446,160,896 B | none (no theorems) |
| LDM-04 | AspisJoinedMeasure, walk extended to constructors and recursors of every inductive type reached | 29e932021ac8d32d0fa24545a1ce5b04fd39c18022c9586862c12e694ba3d49a | 0 | 11.54 s | 4,312,940 KB | 428,302,336 B | none (no theorems) |

LDM-04 answers the reviewer's caveat on the walk. With constructors and recursors visited it
reaches the same 1,003 project modules, 11,958 project constants (64 more), and no class iii
module.

All `#print axioms` lines of LDJ-02 to LDJ-05 (32 of them) are `[propext, Classical.choice,
Quot.sound]`. No warnings. These are focused compiles against cached objects, not a coherent
rebuild of the closure; that rebuild is owed before any claim.
