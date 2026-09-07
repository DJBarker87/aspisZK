import AspisFormal.K1.V7Tag73ExactRestoredCleanPairFactorization
import AspisFormal.K1.V7Tag73ExactRestoredQ16SemanticNoninterference

/-!
# Semantic endpoint for the sound restored K1.3 pair factorization

The probability theorem fixes the residual/alpha context and both positioned
work answers.  This file states the exact deterministic source consequence and
proves that it is sufficient for equality of the restored consistency sets.
No q16 coordinate occurs in the semantic premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactRestoredCleanPairSemanticNoninterference

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredCleanPairFactorization
open AspisK1.V7Tag73ExactRestoredQ16ResidualFactorization
open AspisK1.V7Tag73ExactRestoredQ16SemanticNoninterference
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73Q16RawENNRealProbability
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- The precise source theorem left after the 518-coordinate factorization.
The restored consistency set reads exactly these four fields. -/
def ExactRestoredRootCleanK13PairSemanticInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactRestoredRootCleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left)
          foldTrial finalTrial)
      (rightWitness : ExactRestoredRootCleanK13PairTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right)
          foldTrial finalTrial),
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.1) →
    (let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
      transitionFuel foldTrial.val finalTrial.val
      (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        left).2.2.1 =
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
        right).2.2.1) →
    leftWitness.joint.k12.words = rightWitness.joint.k12.words ∧
      (exactRestoredRootK13View leftWitness.joint.input).gamma =
        (exactRestoredRootK13View rightWitness.joint.input).gamma ∧
      (exactRestoredRootK13View leftWitness.joint.input).disclosedFinal =
        (exactRestoredRootK13View rightWitness.joint.input).disclosedFinal ∧
      (exactRestoredRootK13View leftWitness.joint.input).schedule =
        (exactRestoredRootK13View rightWitness.joint.input).schedule

/-- The semantic source endpoint is exactly sufficient for the pointwise bad
set invariant consumed by the probability package. -/
theorem exact_restored_clean_k13_pair_coordinate_invariant_of_semantic
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (semantic : ExactRestoredRootCleanK13PairSemanticInvariant transitionFuel
      configuration projection fixedInstance decoder) :
    ExactRestoredRootCleanK13PairCoordinateInvariant transitionFuel configuration
      projection fixedInstance decoder := by
  intro foldTrial finalTrial hidden left right leftMember rightMember
  dsimp only
  intro contextExact foldExact workExact
  change Nonempty (ExactRestoredRootCleanK13PairTrialWitness transitionFuel
    configuration projection fixedInstance decoder (hidden, left) foldTrial
      finalTrial) at leftMember
  change Nonempty (ExactRestoredRootCleanK13PairTrialWitness transitionFuel
    configuration projection fixedInstance decoder (hidden, right) foldTrial
      finalTrial) at rightMember
  let leftWitness := Classical.choice leftMember
  let rightWitness := Classical.choice rightMember
  obtain ⟨wordsExact, gammaExact, finalExact, scheduleExact⟩ :=
    semantic foldTrial finalTrial hidden left right leftWitness rightWitness
      contextExact foldExact workExact
  have intrinsicExact :=
    exact_restored_root_k13_intrinsic_bad_congr_of_semantic_fields decoder
      leftWitness.joint.input rightWitness.joint.input
      leftWitness.joint.k12.words rightWitness.joint.k12.words wordsExact
        gammaExact finalExact scheduleExact
  have badExact : leftWitness.joint.bad = rightWitness.joint.bad := by
    rw [leftWitness.joint.badExact, rightWitness.joint.badExact]
    exact intrinsicExact
  have leftPointwise :
      exactRestoredRootCleanK13PairPointwiseBad transitionFuel configuration
        projection fixedInstance decoder foldTrial finalTrial (hidden, left) =
          leftWitness.joint.bad := by
    simpa [exactRestoredRootCleanK13PairPointwiseBad, leftMember, leftWitness]
  have rightPointwise :
      exactRestoredRootCleanK13PairPointwiseBad transitionFuel configuration
        projection fixedInstance decoder foldTrial finalTrial (hidden, right) =
          rightWitness.joint.bad := by
    simpa [exactRestoredRootCleanK13PairPointwiseBad, rightMember, rightWitness]
  exact leftPointwise.trans (badExact.trans rightPointwise.symm)

/-- Release-shaped probability consequence.  Its sole protocol-specific input
is now the deterministic semantic invariant above. -/
theorem exact_restored_clean_trial_union_probability_le_one_forest_of_semantic
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
    (finalExposureCap : unifiedFull256ExposureCap parameters ≤ 2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          ⋃ finalTrial : ExactCompilerExposureTrial parameters,
            exactRestoredRootK13JointTrialEvent transitionFuel configuration
              projection fixedInstance decoder finalTrial) ≤
      q16SemanticOneForestRawError := by
  exact exact_restored_clean_trial_union_probability_le_one_forest hiddenLaw
    transitionRoom programmedCover frontierExact
      (exact_restored_clean_k13_pair_coordinate_invariant_of_semantic semantic)
      reference traceExists foldExposureCap finalExposureCap

#print axioms ExactRestoredRootCleanK13PairSemanticInvariant
#print axioms exact_restored_clean_k13_pair_coordinate_invariant_of_semantic
#print axioms
  exact_restored_clean_trial_union_probability_le_one_forest_of_semantic

end

end AspisK1.V7Tag73ExactRestoredCleanPairSemanticNoninterference
