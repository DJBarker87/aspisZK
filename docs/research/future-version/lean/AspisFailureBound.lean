import AspisChargedHitMass40
import AspisAcceptanceLinkR40
import AspisRec40CallBudgetAspis
import AspisLib_Recorded
import BinCombinedMerkleCollision
import QueryScanModelFailure

/-! End-to-end assembly of the model-level failure bound for the Aspis 40-row
one-phase experiment (form (P) of ASPIS-FAILURE-BOUND.md): decision
`AspisOneTx.dV_aspis`, classifier `classifier40 AspisOneTx.decodePairS`,
R1's failure observable `failureMass` (accepted and R1's extractor returns no
witness) and R1's extractor-abort allowance.

The pieces not yet proved are hypotheses, each a named proposition below:
* `AcceptedChecks40`: accepted and no collision give the Aspis checks on the
  40-row transcript of the run (R1's `fibre_checks`/`accepted_facts`, first
  conjunct, for `dV_aspis`);
* `WordAlignment40`: R1's extractor's word re-enrichment is the identity on
  an accepted collision-free run (R1's `extractor_word_alignment`);
* `HitInPrefix40`: a hit of the Aspis classifier in the run's 40-row
  transcript is a hit in the recovered charged prefix (R1's
  `Frozen2StartChargeCompletion.{decodes, hit_in_prefix}` with format/tag).

Discharged here or reused: the start term (`restricted_union_bound_weighted40`),
the collision term (`BinCombinedMerkleCollision.mass` at the rows agent's
`projected_first_reads`, `Q + 1111`), the step from Aspis checks and no Aspis
hit to R1's checks and R1's no-hit on the first 33 rounds
(`aspis_checks_noHit_r1_checks`, `transcript_take33`), the extractor abort
(R1's `shared_oracle_failure_le_supplied_hit_bound`, unchanged), the query
scan (R1's `QueryScanModelFailure.exhaustion_bound`, unchanged).

Kind of result: a conditional model theorem. It is not a bound on the
deployed program, has no account term and no payout conjunct, and no figure
follows from it while the three hypotheses are open. -/
set_option autoImplicit false
noncomputable section
namespace AspisFailureBound
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1 OraclePortStoredExperimentC4 RawRecordedOracleExtractionMassBin
open AspisCharge40 AspisRowStarts40 AspisPerStep.RowStarts
attribute [local irreducible] R0C.V3.hitsChain3 GenericNoHit.hitFrom LiteralClassifier.bad
  AspisAcceptance.bad

/-- The Aspis full experiment at the one-transaction decision. -/
abbrev exp (D : LiteralByteProtocol.Decoder) (P : Prover) :=
  AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P

/-- The same program at R1's experiment type (`Experiment`), so that runs
carry R1's carrier types, as in `CleanAcceptedModel`. -/
abbrev expE (D : LiteralByteProtocol.Decoder) (P : Prover) : Experiment := exp D P

/-- A run at R1's experiment type. -/
abbrev Run := List (Bytes × State) ×
  ((LiteralTranscript.Public × (Nat → LiteralTranscript.Message)) × Bool)

/-- The Aspis 40-row transcript of a run. -/
abbrev rounds40 (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (run : Run) :=
  ((AspisRows40.Protocol.protocol D).transcript H run.2.1.1 run.2.1.2 40).rounds

/-- The exceptional event: R1's collision event at `Q + 1111` or a prefix hit
of the Aspis classifier. -/
def bad40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (run : RawCutProverCompiler.RunView) : Prop :=
  AspisR1.AspisLib.RecordedBinaryExperimentBin.binaryCollision (Q+1111) run ∨
    AspisRec40.HitMass.prefixHit (classifier40 AspisOneTx.decodePairS) D P run

/-- Open hypothesis 1 (acceptance to checks at experiment level). -/
def AcceptedChecks40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat) : Prop :=
  ∀ H : Bytes → State,
    (eval H (expE D P)).2.2 = true →
    ¬ AspisR1.AspisLib.RecordedBinaryExperimentBin.binaryCollision (Q+1111) (eval H (expE D P)) →
    Nonempty (AspisAcceptance.AspisChecks AspisOneTx.decodePairS (eval H (expE D P)).2.1.1
      (rounds40 D H (eval H (expE D P))))

/-- Open hypothesis 2 (extractor word alignment). -/
def WordAlignment40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat) : Prop :=
  ∀ H : Bytes → State,
    (eval H (expE D P)).2.2 = true →
    ¬ AspisR1.AspisLib.RecordedBinaryExperimentBin.binaryCollision (Q+1111) (eval H (expE D P)) →
    RawCutTranscriptRun.proof (RawCutWordsFromRunExecutableBin.wordsFromRun (eval H (expE D P)))
      (eval H (expE D P)).2.1.2 = (eval H (expE D P)).2.1.2

/-- Open hypothesis 3 (a transcript hit is a charged-prefix hit). -/
def HitInPrefix40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat) : Prop :=
  ∀ H : Bytes → State,
    (eval H (expE D P)).2.2 = true →
    ¬ AspisR1.AspisLib.RecordedBinaryExperimentBin.binaryCollision (Q+1111) (eval H (expE D P)) →
    GenericNoHit.hitFrom (AspisAcceptance.bad AspisOneTx.decodePairS) (eval H (expE D P)).2.1.1 []
      (rounds40 D H (eval H (expE D P))) →
    AspisRec40.HitMass.prefixHit (classifier40 AspisOneTx.decodePairS) D P (eval H (expE D P))

/-- The step at one run: Aspis checks and no Aspis hit on the 40-row
transcript give R1's checks and R1's no-hit on R1's 33-row transcript at the
re-enriched proof. -/
theorem clean_core (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf pf' : LiteralByteProtocol.Proof) (hw : pf' = pf)
    (c : AspisAcceptance.AspisChecks AspisOneTx.decodePairS pub
      ((AspisRows40.Protocol.protocol D).transcript H pub pf 40).rounds)
    (hno : ¬ GenericNoHit.hitFrom (AspisAcceptance.bad AspisOneTx.decodePairS) pub []
      ((AspisRows40.Protocol.protocol D).transcript H pub pf 40).rounds) :
    ∃ _checks : LiteralAcceptanceTerminal.Checks pub
        ((LiteralByteProtocol.protocol D).transcript H pub pf' 33).rounds,
      ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub []
        ((LiteralByteProtocol.protocol D).transcript H pub pf' 33).rounds := by
  subst hw
  obtain ⟨⟨checks⟩, hno33⟩ :=
    AspisAcceptance.aspis_checks_noHit_r1_checks AspisOneTx.decodePairS _ _ c hno
  have hpre := (AspisRows40.Literal.transcript_take33 D
    (fun pub _ => GenericNoHit.chooseWitness LiteralProtocol.relation pub) H pub pf' 40
    (by omega)).2
  rw [hpre] at checks hno33
  exact ⟨checks, hno33⟩

/-- The clean event at one oracle, with the run generalised before any step
(no reduction of the experiment's evaluation is needed). -/
theorem clean40_at (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (g1 : AcceptedChecks40 D P Q) (g2 : WordAlignment40 D P Q) (g3 : HitInPrefix40 D P Q)
    (H : Bytes → State) :
    (eval H (expE D P)).2.2 = true → ¬ bad40 D P Q (eval H (expE D P)) →
      ∃ _checks : LiteralAcceptanceTerminal.Checks (eval H (expE D P)).2.1.1
          ((LiteralByteProtocol.protocol D).transcript H (eval H (expE D P)).2.1.1
            (RawCutTranscriptRun.proof (RawCutWordsFromRunExecutableBin.wordsFromRun
              (eval H (expE D P))) (eval H (expE D P)).2.1.2) 33).rounds,
        ¬ GenericNoHit.hitFrom LiteralClassifier.bad (eval H (expE D P)).2.1.1 []
          ((LiteralByteProtocol.protocol D).transcript H (eval H (expE D P)).2.1.1
            (RawCutTranscriptRun.proof (RawCutWordsFromRunExecutableBin.wordsFromRun
              (eval H (expE D P))) (eval H (expE D P)).2.1.2) 33).rounds := by
  have h1 := g1 H
  have h2 := g2 H
  have h3 := g3 H
  unfold rounds40 at h1 h3
  generalize eval H (expE D P) = run at h1 h2 h3 ⊢
  intro ha hn
  have hc : ¬ AspisR1.AspisLib.RecordedBinaryExperimentBin.binaryCollision (Q+1111) run :=
    fun h => hn (Or.inl h)
  have hh : ¬ AspisRec40.HitMass.prefixHit (classifier40 AspisOneTx.decodePairS) D P run :=
    fun h => hn (Or.inr h)
  obtain ⟨c⟩ := h1 ha hc
  exact clean_core D H run.2.1.1 run.2.1.2 _ (h2 ha hc) c (fun hit => hh (h3 ha hc hit))

/-- The clean event for Aspis in R1's form, from the three hypotheses. -/
theorem clean40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (g1 : AcceptedChecks40 D P Q) (g2 : WordAlignment40 D P Q) (g3 : HitInPrefix40 D P Q) :
    CleanAcceptedModel D (expE D P) (bad40 D P Q) :=
  fun H => clean40_at D P Q g1 g2 g3 H

/-- Form (P), model part: R1's `failure_bound` shape for the Aspis experiment,
conditional on the three open hypotheses. -/
theorem failure_bound40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (g1 : AcceptedChecks40 D P Q) (g2 : WordAlignment40 D P Q) (g3 : HitInPrefix40 D P Q) :
    lazyMean (exp D P) emptyTable failureMass ≤
      BinCombinedMerkleCollision.kappa (Q+1111) +
        ((Q : ℚ) * capMax + verifierCharge40) + 1/(2:ℚ)^126 := by
  have hc := BinCombinedMerkleCollision.mass SelectedTranscriptParams.params.iv
    (Q+1111) (exp D P) (AspisRec40.CallBudgetAspis.projected_first_reads D P Q hq)
  have hs := AspisPerStep.ChargedHitMass40.restricted_union_bound_weighted40
    AspisOneTx.decodePairS D AspisOneTx.dV_aspis P Q hq
  apply shared_oracle_failure_le_supplied_hit_bound D (exp D P) (bad40 D P Q)
    (clean40 D P Q g1 g2 g3)
  calc
    lazyMean (exp D P) emptyTable (fun run => indicator (bad40 D P Q run)) ≤
        lazyMean (exp D P) emptyTable (fun run =>
          indicator (AspisR1.AspisLib.RecordedBinaryExperimentBin.binaryCollision (Q+1111) run) +
          indicator (AspisRec40.HitMass.prefixHit (classifier40 AspisOneTx.decodePairS) D P run)) :=
      AllAddressFiatShamir.lazyMean_mono_of_eval _ _ _ (fun _ => indicator_or_le _ _)
    _ = _ := lazyMean_add _ _ _ _
    _ ≤ _ := add_le_add hc hs

/-- Form (P): with R1's query-scan allowance added as in R1's `failureModel`. -/
theorem failure_bound40P (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (g1 : AcceptedChecks40 D P Q) (g2 : WordAlignment40 D P Q) (g3 : HitInPrefix40 D P Q) :
    lazyMean (exp D P) emptyTable failureMass + QueryScanModelFailure.failureProbability (2^18) ≤
      BinCombinedMerkleCollision.kappa (Q+1111) +
        ((Q : ℚ) * capMax + verifierCharge40) + 1/(2:ℚ)^126 + 1/(2:ℚ)^454 :=
  add_le_add (failure_bound40 D P Q hq g1 g2 g3) QueryScanModelFailure.exhaustion_bound

#print axioms clean_core
#print axioms clean40_at
#print axioms clean40
#print axioms failure_bound40
#print axioms failure_bound40P
end AspisFailureBound
end
