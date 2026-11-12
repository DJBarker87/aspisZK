import AspisRec40CleanA
import AspisRec40FinalShape
import AspisRec40CleanB
import AspisRec40CleanTag
import AspisRec40CleanWords
import AspisRec40CleanRun
import AspisRec40CallBudgetAspis

/-! Aspis 40-row clean event: `clean40`, R1's `Frozen2StartChargeClean.clean`
for the 40-row experiment at the one-transaction decision `dV_aspis`.

Two named hypotheses, with exactly the shapes stated in
`AspisRec40CleanStatement` / RECORDED-EXPERIMENT-40.md §7.2:
* `hchecks`: `CheckedAcceptance40` at every stored input (the game agent's
  M9; R1's `fibre_checks`). It is stated at `ChargePrefix.prover P`, which is
  R1's `pairProver s P` as a program (R1's `Frozen2StartChargePrefix.fibre_prover`).
* `hfinal`: decoding of rows 33 to 39 on the charged run, under R1's four
  premises of `Frozen2StartChargeCompletion.decodes` (mine, to be discharged).
Everything else is proved here: the full experiment equals the recorded
decision experiment, acceptance and output transport, the constructor
schedule and `Format` from `AspisChecks` fields, the public tag from
`admitted_aspis`/`accepted_guardS`, the word alignment, and the assembly. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.Clean
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisR1 OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open RawCutProverCompiler (experiment)
open CanonicalCutEnrichedTranscript (Words enrichMessage)

abbrev pr (D : LiteralByteProtocol.Decoder) := AspisRows40.Protocol.protocol D

attribute [local irreducible] R0C.V3.hitsChain3 GenericNoHit.hitFrom LiteralClassifier.bad
  AspisAcceptance.bad AspisOneTx.dV_aspis

/-! ## Accepted facts and the clean event -/

/-- Copy of `Frozen2StartChargeClean.accepted_facts`, under `hchecks`. -/
theorem accepted_facts (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hchecks : ∀ s, AspisRec40.CleanStatement.CheckedAcceptance40 D (AspisOneTx.dV_aspis s)
      (AspisRec40.ChargePrefix.prover P) (Q+1111))
    (H : Bytes → State)
    (hc : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1111)
      (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)))
    (ha : (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).2.2 = true) :
    ∃ checks : AspisAcceptance.AspisChecks AspisOneTx.decodePairS
        (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).2.1.1
        ((pr D).transcript H (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).2.1.1
          (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).2.1.2 40).rounds,
      RawCutTranscriptRun.proof (RawCutWordsFromRunExecutableBin.wordsFromRun
        (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)))
        (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).2.1.2 =
        (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).2.1.2 ∧
      (eval H (AspisRec40.ChargePrefix.base D P)).2.1.1.tag = 2 := by
  let s := (eval H P).2.stored
  let d := AspisOneTx.dV_aspis s
  have same := AspisRec40.CleanA.projected_eq_recorded D AspisOneTx.dV_aspis P H
  have hcf : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1111)
      (eval H (AspisRec40.Decision.recorded D d (AspisRec40.ChargePrefix.prover P))) := by
    rw [← same]; exact hc
  have haf : (eval H (AspisRec40.Decision.original D d (AspisRec40.ChargePrefix.prover P))).2.2 = true := by
    rw [← AspisRec40.CleanA.recorded_accepts, ← same]; exact ha
  obtain ⟨checks⟩ := hchecks s H hcf haf
  have fixed := (AspisRec40.CleanWords.extractor_word_alignment D d (AspisRec40.ChargePrefix.prover P) H checks).2
  have tag : (eval H (AspisRec40.ChargePrefix.prover P)).2.1.tag = 2 :=
    AspisRec40.CleanTag.accepted_tag D s _ H haf
  refine ⟨?_, ?_, ?_⟩
  · rw [same]; exact checks
  · rw [same]; exact fixed
  · rw [AspisRec40.ChargePrefix.base, RawCutProverCompiler.experiment_eval]
    exact tag

/-- Copy of `Frozen2StartChargeClean.clean`: the Aspis clean event, conditional on
`hchecks` (game agent, M9) and `hfinal` (rows 33 to 39 decoding). -/
theorem clean40 (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (hchecks : ∀ s, AspisRec40.CleanStatement.CheckedAcceptance40 D (AspisOneTx.dV_aspis s)
      (AspisRec40.ChargePrefix.prover P) (Q+1111))
    (hfinal : ∀ H : Bytes → State,
      firstReads emptyTable (eval H (AspisRec40.ChargePrefix.base D P)).1 ≤ Q+1111 →
      ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
          BinRawByteCollisionTargets.pred (Q+1111)) emptyTable
          (eval H (AspisRec40.ChargePrefix.base D P)).1 →
      RWireCheckedFormat.Format (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 →
      (eval H (AspisRec40.ChargePrefix.base D P)).2.1.1.tag = 2 →
      AspisRec40.FinalShape.LatePayload (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 →
      AspisRec40.CleanStatement.FinalDecodes D H (eval H (AspisRec40.ChargePrefix.charged D P))) :
    AspisRec40.CleanStatement.CleanAcceptedModel40 D
      (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)
      (AspisRec40.CleanStatement.bad40 D P Q) := by
  intro H run ha hn
  have hc : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1111)
      (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)) := fun h => hn (Or.inl h)
  have hh : ¬ AspisRec40.HitMass.prefixHit (AspisCharge40.classifier40 AspisOneTx.decodePairS) D P
      (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)) := fun h => hn (Or.inr h)
  obtain ⟨checks, fixed, tag⟩ := accepted_facts D P Q hchecks H hc ha
  have format := AspisRec40.CleanB.format_of_checks D H _ _ checks
  rw [AspisRec40.CleanA.same_transcript, AspisRec40.ChargePrefix.charged_eval] at format
  have fmt : RWireCheckedFormat.Format (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 :=
    RWireCheckedFormat.format_of_enrich _ _ format
  obtain ⟨tail, htail⟩ := AspisRec40.HitMass.chronological_prefix D AspisOneTx.dV_aspis P H
  have fullReads := AspisRec40.CallBudgetAspis.projected_first_reads D P Q hq H
  have hQ : firstReads emptyTable (eval H (AspisRec40.ChargePrefix.base D P)).1 ≤ Q+1111 := by
    have h := TraceAppend.firstReads_le_append emptyTable
      (eval H (AspisRec40.ChargePrefix.charged D P)).1 tail
    rw [← htail, AspisRec40.ChargePrefix.charged_eval] at h
    exact h.trans fullReads
  have hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1111)) emptyTable
      (eval H (AspisRec40.ChargePrefix.base D P)).1 := by
    intro h
    apply hc
    change hitsBad _ emptyTable (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).1
    rw [htail, AspisRec40.ChargePrefix.charged_eval]
    exact TraceAppend.hitsBad_of_prefix _ _ _ _ h
  have hlate : AspisRec40.FinalShape.LatePayload (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 := by
    have h0 := AspisRec40.FinalShape.latePayload_of_checks D H _ _ checks
    have h1 : (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).2.1.2 =
        (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.2 :=
      congrArg (fun x => x.2) (AspisRec40.CleanA.same_transcript D AspisOneTx.dV_aspis P H)
    rw [h1, AspisRec40.ChargePrefix.charged_eval] at h0
    exact (AspisRec40.FinalShape.latePayload_enrich _ _).1 h0
  have hd := AspisRec40.CleanRun.decodes40 D P H (Q+1111) hQ hout fmt tag
    (hfinal H hQ hout fmt tag hlate)
  refine ⟨?_, ?_⟩
  · rw [fixed]; exact checks
  · rw [fixed]
    intro hit
    have hit' : GenericNoHit.hitFrom (AspisAcceptance.bad AspisOneTx.decodePairS)
        (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.1 []
        ((pr D).transcript H (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.1
          (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.2 (pr D).r).rounds := by
      rw [← AspisRec40.CleanA.same_transcript D AspisOneTx.dV_aspis P H]
      exact hit
    apply hh
    change hitsChain3 _ _ _ (AspisRec40.HitMass.recovered D P
      (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P))).1
    rw [AspisRec40.HitMass.recovered_eval]
    exact AspisRec40.CleanRun.hit_in_prefix D P H hd hit'

#print axioms accepted_facts
#print axioms clean40

/-- The hit step of `clean40` on its own (the shape of the assembly's
`HitInPrefix40`): accepted, no collision and a hit of the Aspis classifier in
the run's 40-row transcript give a prefix hit of the charged run. -/
theorem hit_in_prefix_of (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (hchecks : ∀ s, AspisRec40.CleanStatement.CheckedAcceptance40 D (AspisOneTx.dV_aspis s)
      (AspisRec40.ChargePrefix.prover P) (Q+1111))
    (hfinal : ∀ H : Bytes → State,
      firstReads emptyTable (eval H (AspisRec40.ChargePrefix.base D P)).1 ≤ Q+1111 →
      ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
          BinRawByteCollisionTargets.pred (Q+1111)) emptyTable
          (eval H (AspisRec40.ChargePrefix.base D P)).1 →
      RWireCheckedFormat.Format (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 →
      (eval H (AspisRec40.ChargePrefix.base D P)).2.1.1.tag = 2 →
      AspisRec40.FinalShape.LatePayload (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 →
      AspisRec40.CleanStatement.FinalDecodes D H (eval H (AspisRec40.ChargePrefix.charged D P)))
    (H : Bytes → State)
    (ha : (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).2.2 = true)
    (hc : ¬ RecordedBinaryExperimentBin.binaryCollision (Q+1111)
      (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)))
    (hit : GenericNoHit.hitFrom (AspisAcceptance.bad AspisOneTx.decodePairS)
      (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).2.1.1 []
      ((pr D).transcript H (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).2.1.1
        (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).2.1.2 40).rounds) :
    AspisRec40.HitMass.prefixHit (AspisCharge40.classifier40 AspisOneTx.decodePairS) D P
      (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)) := by
  obtain ⟨checks, _, tag⟩ := accepted_facts D P Q hchecks H hc ha
  have format := AspisRec40.CleanB.format_of_checks D H _ _ checks
  rw [AspisRec40.CleanA.same_transcript, AspisRec40.ChargePrefix.charged_eval] at format
  have fmt : RWireCheckedFormat.Format (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 :=
    RWireCheckedFormat.format_of_enrich _ _ format
  obtain ⟨tail, htail⟩ := AspisRec40.HitMass.chronological_prefix D AspisOneTx.dV_aspis P H
  have fullReads := AspisRec40.CallBudgetAspis.projected_first_reads D P Q hq H
  have hQ : firstReads emptyTable (eval H (AspisRec40.ChargePrefix.base D P)).1 ≤ Q+1111 := by
    have h := TraceAppend.firstReads_le_append emptyTable
      (eval H (AspisRec40.ChargePrefix.charged D P)).1 tail
    rw [← htail, AspisRec40.ChargePrefix.charged_eval] at h
    exact h.trans fullReads
  have hout : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1111)) emptyTable
      (eval H (AspisRec40.ChargePrefix.base D P)).1 := by
    intro h
    apply hc
    change hitsBad _ emptyTable (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).1
    rw [htail, AspisRec40.ChargePrefix.charged_eval]
    exact TraceAppend.hitsBad_of_prefix _ _ _ _ h
  have hlate : AspisRec40.FinalShape.LatePayload (eval H (AspisRec40.ChargePrefix.base D P)).2.1.2 := by
    have h0 := AspisRec40.FinalShape.latePayload_of_checks D H _ _ checks
    have h1 : (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P)).2.1.2 =
        (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.2 :=
      congrArg (fun x => x.2) (AspisRec40.CleanA.same_transcript D AspisOneTx.dV_aspis P H)
    rw [h1, AspisRec40.ChargePrefix.charged_eval] at h0
    exact (AspisRec40.FinalShape.latePayload_enrich _ _).1 h0
  have hd := AspisRec40.CleanRun.decodes40 D P H (Q+1111) hQ hout fmt tag
    (hfinal H hQ hout fmt tag hlate)
  have hit' : GenericNoHit.hitFrom (AspisAcceptance.bad AspisOneTx.decodePairS)
      (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.1 []
      ((pr D).transcript H (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.1
        (eval H (AspisRec40.ChargePrefix.charged D P)).2.1.2 (pr D).r).rounds := by
    rw [← AspisRec40.CleanA.same_transcript D AspisOneTx.dV_aspis P H]
    exact hit
  change hitsChain3 _ _ _ (AspisRec40.HitMass.recovered D P
    (eval H (AspisRec40.HitMass.projected D AspisOneTx.dV_aspis P))).1
  rw [AspisRec40.HitMass.recovered_eval]
  exact AspisRec40.CleanRun.hit_in_prefix D P H hd hit'

#print axioms hit_in_prefix_of

end AspisRec40.Clean
end
