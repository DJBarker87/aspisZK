import AspisFormal.K1.V7Tag73ExactConcreteK12Bound
import AspisFormal.K1.V7Tag73ExactRestoredOperationalK13OneFoldProbability
import AspisFormal.K1.V7Tag73ExactRestoredOperationalK13QueryProbability
import AspisFormal.K1.V7Tag73K13IdealErrorLedger

/-!
# Measured restoration-wide K1.3 composition

This is the event-algebra endpoint for the corrected restoration-wide K1.3
classifier.  The q16 term is discharged internally by the sound 518-coordinate
pair factorization.  The remaining source work is separated into the exact
Merkle, one-fold and ideal-relation event bounds rather than hidden behind one
conclusion-shaped K1.3 premise.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredOperationalK13MeasuredComposition

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK12Bound
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredCleanPairSemanticNoninterference
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactRestoredOperationalK13Events
open AspisK1.V7Tag73ExactRestoredOperationalK13OneFoldProbability
open AspisK1.V7Tag73ExactRestoredOperationalK13QueryProbability
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Exact raw error charged to the corrected restoration-wide K1.3 stage.
K1.2 is administrative in that stage package, so its two-tree term is included
here exactly once. -/
def exactRestoredOperationalK13RawError
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters) :
    ENNReal :=
  exactTag73K12ErrorBound configuration + q16SemanticOneForestRawError +
    exactOneFoldIdealRawError + exactJointQueryBatchIdealRawError +
      exactLaterRelationAlphaIdealRawError

/-- The canonical list-cap event is empty for the exact production encoder. -/
theorem exact_restored_operational_canonical_root_k13_list_cap_event_eq_empty
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder) :
    exactTag73RestoredOperationalCanonicalRootK13ListCapEvent transitionFuel
        configuration projection fixedInstance decoder = ∅ := by
  ext sample
  constructor
  · intro member
    rcases member with ⟨input, k12, failure⟩
    have rootMember : sample ∈
        exactTag73RestoredOperationalRootK13ListCapEvent transitionFuel
          configuration projection fixedInstance decoder :=
      ⟨input, k12.words, failure⟩
    rw [exact_restored_operational_root_k13_list_cap_event_eq_empty
      initialEncoderExact] at rootMember
    exact rootMember
  · simp

/-- Compiler-clean measured bound for the actual restoration-wide K1.3
classifier.  q16 and the degree-three one-fold probability theorem are proved
internally.  The remaining premises are the literal Merkle/relation bounds and
the pre-answer one-fold source family that subsequent source leaves discharge.
-/
theorem exact_restored_operational_k13_clean_error_measure_bound
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (frontierExact : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (schedule : QuerySchedule),
      (exactOperationalTape input).frontierNodes schedule =
        semanticFrontierNodes schedule.positions)
    (semantic : ExactRestoredRootCleanK13PairSemanticInvariant transitionFuel
      configuration projection fixedInstance decoder)
    (reference : AdmittedResult SemanticCap203Admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput SemanticCap203Admitted 64
        reference.1))
    (foldExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 31)
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (merkleBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            (exactTag73RestoredOperationalRootK12AuthenticationEvent
                transitionFuel configuration projection fixedInstance ∪
              exactTag73RestoredOperationalRootK12ExtractionEvent
                transitionFuel configuration projection fixedInstance)) ≤
        exactTag73K12ErrorBound configuration)
    (idealBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
              projection fixedInstance ∩
            (exactTag73RestoredOperationalK13FailureEvent transitionFuel
                configuration projection fixedInstance decoder ∩
              exactTag73RestoredOperationalCanonicalRootK13IdealRejectedEvent
                transitionFuel configuration projection fixedInstance decoder)) ≤
        exactJointQueryBatchIdealRawError +
          exactLaterRelationAlphaIdealRawError)
    (oneFoldSource : ExactTag73RestoredCanonicalOneFoldSource transitionFuel
      configuration projection fixedInstance decoder
      (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
        projection fixedInstance)) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          exactTag73RestoredOperationalK13FailureEvent transitionFuel
            configuration projection fixedInstance decoder) ≤
      exactRestoredOperationalK13RawError configuration := by
  let law := exactCompilerJointLaw hiddenLaw parameters
  let clean := exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
    projection fixedInstance
  let authentication :=
    exactTag73RestoredOperationalRootK12AuthenticationEvent transitionFuel
      configuration projection fixedInstance
  let extraction := exactTag73RestoredOperationalRootK12ExtractionEvent
    transitionFuel configuration projection fixedInstance
  let ideal := exactTag73RestoredOperationalCanonicalRootK13IdealRejectedEvent
    transitionFuel configuration projection fixedInstance decoder
  let failure := exactTag73RestoredOperationalK13FailureEvent transitionFuel
    configuration projection fixedInstance decoder
  let query := exactTag73RestoredOperationalCanonicalRootK13QueryEvent
    transitionFuel configuration projection fixedInstance decoder
  let oneFold := exactTag73RestoredOperationalCanonicalRootK13OneFoldEvent
    transitionFuel configuration projection fixedInstance decoder
  let listCap := exactTag73RestoredOperationalCanonicalRootK13ListCapEvent
    transitionFuel configuration projection fixedInstance decoder
  have covered :
      clean ∩ exactTag73RestoredOperationalK13FailureEvent transitionFuel
          configuration projection fixedInstance decoder ⊆
        (((clean ∩ (authentication ∪ extraction)) ∪
            (clean ∩ (failure ∩ ideal))) ∪
          (clean ∩ query)) ∪ ((clean ∩ oneFold) ∪ (clean ∩ listCap)) := by
    rintro sample ⟨cleanMember, failure⟩
    have classified :=
      exact_restored_operational_k13_failure_subset_canonical_root_complete
        failure
    change sample ∈ (((authentication ∪ extraction) ∪ ideal) ∪ query) ∪
      (oneFold ∪ listCap) at classified
    rcases classified with (((authenticationMember | extractionMember) |
        idealMember) | queryMember) | (oneFoldMember | listCapMember)
    · exact Or.inl (Or.inl (Or.inl
        ⟨cleanMember, Or.inl authenticationMember⟩))
    · exact Or.inl (Or.inl (Or.inl
        ⟨cleanMember, Or.inr extractionMember⟩))
    · exact Or.inl (Or.inl (Or.inr
        ⟨cleanMember, failure, idealMember⟩))
    · exact Or.inl (Or.inr ⟨cleanMember, queryMember⟩)
    · exact Or.inr (Or.inl ⟨cleanMember, oneFoldMember⟩)
    · exact Or.inr (Or.inr ⟨cleanMember, listCapMember⟩)
  have queryBound :=
    exact_restored_operational_canonical_root_k13_query_probability_le
      hiddenLaw transitionRoom programmedCover frontierExact semantic reference
        traceExists foldExposureCap finalExposureCap
  have oneFoldBound :=
    exact_restored_operational_canonical_root_k13_onefold_probability_le
      hiddenLaw clean oneFoldSource
  have listCapEmpty : listCap = ∅ := by
    exact exact_restored_operational_canonical_root_k13_list_cap_event_eq_empty
      initialEncoderExact
  calc
    law.toOuterMeasure
        (clean ∩ exactTag73RestoredOperationalK13FailureEvent transitionFuel
          configuration projection fixedInstance decoder) ≤
      law.toOuterMeasure
        ((((clean ∩ (authentication ∪ extraction)) ∪
            (clean ∩ (failure ∩ ideal))) ∪
          (clean ∩ query)) ∪ ((clean ∩ oneFold) ∪ (clean ∩ listCap))) :=
        measure_mono covered
    _ ≤ ((law.toOuterMeasure (clean ∩ (authentication ∪ extraction)) +
            law.toOuterMeasure (clean ∩ (failure ∩ ideal))) +
          law.toOuterMeasure (clean ∩ query)) +
        (law.toOuterMeasure (clean ∩ oneFold) +
          law.toOuterMeasure (clean ∩ listCap)) := by
      calc
        _ ≤ law.toOuterMeasure
              (((clean ∩ (authentication ∪ extraction)) ∪
                (clean ∩ (failure ∩ ideal))) ∪ (clean ∩ query)) +
            law.toOuterMeasure ((clean ∩ oneFold) ∪
              (clean ∩ listCap)) := measure_union_le _ _
        _ ≤ (law.toOuterMeasure
                ((clean ∩ (authentication ∪ extraction)) ∪
                  (clean ∩ (failure ∩ ideal))) +
              law.toOuterMeasure (clean ∩ query)) +
            (law.toOuterMeasure (clean ∩ oneFold) +
              law.toOuterMeasure (clean ∩ listCap)) :=
          add_le_add (measure_union_le _ _) (measure_union_le _ _)
        _ ≤ _ :=
          add_le_add
            (add_le_add (measure_union_le _ _) le_rfl) le_rfl
    _ ≤ ((exactTag73K12ErrorBound configuration +
            (exactJointQueryBatchIdealRawError +
              exactLaterRelationAlphaIdealRawError)) +
          q16SemanticOneForestRawError) +
        (exactOneFoldIdealRawError + 0) := by
      have listCapZero : law.toOuterMeasure (clean ∩ listCap) = 0 := by
        rw [listCapEmpty]
        simp
      exact add_le_add
        (add_le_add (add_le_add merkleBound idealBound) queryBound)
        (add_le_add oneFoldBound (le_of_eq listCapZero))
    _ = exactRestoredOperationalK13RawError configuration := by
      unfold exactRestoredOperationalK13RawError
      ac_rfl

end


#print axioms exactRestoredOperationalK13RawError
#print axioms
  exact_restored_operational_canonical_root_k13_list_cap_event_eq_empty
#print axioms exact_restored_operational_k13_clean_error_measure_bound

end AspisK1.V7Tag73ExactRestoredOperationalK13MeasuredComposition
