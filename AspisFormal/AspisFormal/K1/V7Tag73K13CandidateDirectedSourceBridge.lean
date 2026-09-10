import AspisFormal.K1.V7Tag73K13CandidateDirectedProbabilityClosure
import AspisFormal.K1.V7Tag73K13CandidateDirectedCoordinateSelected
import AspisFormal.K1.V7Tag73K13RestrictedJointBatchActualLawClosure

/-!
# Component-wise source bridge for candidate-directed K1.3

This replaces a conclusion-shaped event-inclusion premise by literal causal
source facts. The source must expose the accepted work coordinates, the
successful bounded query-batch sampler, and equality of every component of
the finite collision target before that challenge is used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CandidateDirectedSourceBridge

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CandidateDirectedQueryBatchAccounting
open AspisK1.V7Tag73CausalAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16QueryBatchCoordinates
open AspisK1.V7Tag73CausalFoldFinalWorkQueryBatchProbability
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73JointQueryBatchSoundness
open AspisK1.V7Tag73K13CandidateDirectedProbabilityClosure
open AspisK1.V7Tag73K13CandidateDirectedCoordinateSelected
open AspisK1.V7Tag73K13RestrictedJointBatchActualLawClosure
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatProbability
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

theorem exact_candidate_directed_selected_coordinate_components
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {candidate : Q16DigestSlot}
    {foldTrial finalTrial : ExactCompilerExposureTrial parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (selected : ExactTag73CandidateDirectedCoordinateSelected input candidate
      foldTrial finalTrial) :
    let coordinates := exactCandidateDirectedRegroupedCoordinates
      transitionFuel configuration candidate foldTrial finalTrial sample.1
        sample.2
    FoldWork31Accepted coordinates.2.1 ∧
      FinalWork34Accepted coordinates.2.2.1 ∧
      ∃ success : GammaPrefixSucceeds coordinates.2.2.2,
        exactOperationalChallenge input .queryBatch =
          (successfulGammaPrefixFactorization
            ⟨coordinates.2.2.2, success⟩).2.1 := by
  dsimp [ExactTag73CandidateDirectedCoordinateSelected] at selected
  refine ⟨selected.2.2.2.2.1, selected.2.2.2.2.2.1, ?_⟩
  simpa [exactCandidateDirectedRegroupedCoordinates,
    foldFinalWorkQueryBatchCoordinateRegroup,
    successfulGammaPrefixFactorization_value] using selected.2.2.2.2.2.2

/-- Literal production facts at the selected 542-coordinate query-batch
boundary. No event inclusion or measure bound is a field. -/
structure ExactCandidateDirectedK13SourceAlignment
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) where
  view : Q16DigestSlot →
    ExactCompilerExposureTrial parameters →
    ExactCompilerExposureTrial parameters → HiddenTape →
    (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)) →
    Digest256 → Digest256 → VariableGammaCompleteSkeleton →
      JointQueryBatchPreChallengeView
  exactAt : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input)
      (_collisionFacts : ExactTag73K13CollisionCertificate source input k12),
    ∃ candidate foldTrial finalTrial,
      let coordinates := exactCandidateDirectedRegroupedCoordinates
        transitionFuel configuration candidate foldTrial finalTrial sample.1
          sample.2
      FoldWork31Accepted coordinates.2.1 ∧
        FinalWork34Accepted coordinates.2.2.1 ∧
        ∃ success : GammaPrefixSucceeds coordinates.2.2.2,
          let factored := successfulGammaPrefixFactorization
            ⟨coordinates.2.2.2, success⟩
          let currentView := view candidate foldTrial finalTrial sample.1
            coordinates.1 coordinates.2.1 coordinates.2.2.1 factored.1
          exactOperationalChallenge input .queryBatch = factored.2.1 ∧
            currentView.active = true ∧
            currentView.preQueryDiscrepancy =
              source.preQueryDiscrepancy sample input ∧
            currentView.expected =
              exactTag73K13ExpectedQueryVector decoder input k12 ∧
            currentView.authenticated =
              exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
            exactOperationalChallenge input .queryBatch ∈
              currentView.collisionTarget

/-- The remaining production-specific target-data endpoint after scheduler
routing is discharged. It contains no work-acceptance or challenge-generation
premise: those come from the checked 542-coordinate scheduler theorem. -/
structure ExactCandidateDirectedK13ViewAlignment
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder) where
  view : Q16DigestSlot →
    ExactCompilerExposureTrial parameters →
    ExactCompilerExposureTrial parameters → HiddenTape →
    (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)) →
    Digest256 → Digest256 → VariableGammaCompleteSkeleton →
      JointQueryBatchPreChallengeView
  alignedAt : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input)
      (_collisionFacts : ExactTag73K13CollisionCertificate source input k12)
      (candidate : Q16DigestSlot)
      (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
      (_selected : ExactTag73CandidateDirectedCoordinateSelected input candidate
        foldTrial finalTrial),
    let coordinates := exactCandidateDirectedRegroupedCoordinates
      transitionFuel configuration candidate foldTrial finalTrial sample.1
        sample.2
    ∀ success : GammaPrefixSucceeds coordinates.2.2.2,
      let factored := successfulGammaPrefixFactorization
        ⟨coordinates.2.2.2, success⟩
      let currentView := view candidate foldTrial finalTrial sample.1
        coordinates.1 coordinates.2.1 coordinates.2.2.1 factored.1
      currentView.active = true ∧
        currentView.preQueryDiscrepancy =
          source.preQueryDiscrepancy sample input ∧
        currentView.expected =
          exactTag73K13ExpectedQueryVector decoder input k12 ∧
        currentView.authenticated =
          exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
        exactOperationalChallenge input .queryBatch ∈
          currentView.collisionTarget

/-- The checked scheduler and a target-only view alignment construct the full
component-wise source record. -/
noncomputable def ExactCandidateDirectedK13ViewAlignment.toSourceAlignment
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    (alignment : ExactCandidateDirectedK13ViewAlignment transitionFuel
      configuration projection fixedInstance decoder source)
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 542 ≤ 2 * parameters.forkRequestCap) :
    ExactCandidateDirectedK13SourceAlignment transitionFuel configuration
      projection fixedInstance decoder source where
  view := alignment.view
  exactAt := by
    intro sample input k12 collisionFacts
    obtain ⟨foldTrial, finalTrial, candidate, selected⟩ :=
      exact_operational_input_has_candidate_directed_coordinate transitionRoom
        programmedCover input
    obtain ⟨foldAccepted, finalAccepted, success, challengeExact⟩ :=
      exact_candidate_directed_selected_coordinate_components input selected
    obtain ⟨activeExact, preExact, expectedExact, authenticatedExact,
        actualMember⟩ :=
      alignment.alignedAt sample input k12 collisionFacts candidate foldTrial
        finalTrial selected success
    exact ⟨candidate, foldTrial, finalTrial, foldAccepted, finalAccepted,
      success, challengeExact, activeExact, preExact, expectedExact,
      authenticatedExact, actualMember⟩

/-- Component-wise causal source facts instantiate the finite-family source
consumed by the exact probability theorem. -/
noncomputable def ExactCandidateDirectedK13SourceAlignment.toCausalSource
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    (alignment : ExactCandidateDirectedK13SourceAlignment transitionFuel
      configuration projection fixedInstance decoder source) :
    ExactCandidateDirectedK13CausalSource transitionFuel configuration
      projection fixedInstance decoder source where
  target := fun candidate foldTrial finalTrial hidden context fold work
      skeleton =>
    (alignment.view candidate foldTrial finalTrial hidden context fold work
      skeleton).target
  targetCard := by
    intro candidate foldTrial finalTrial hidden context fold work skeleton
    exact (alignment.view candidate foldTrial finalTrial hidden context fold work
      skeleton).target_card_le_sixteen
  collisionMapped := by
    intro sample input k12 collisionFacts
    obtain ⟨candidate, foldTrial, finalTrial, foldAccepted, finalAccepted,
        success, challengeExact, activeExact, _preExact, _expectedExact,
        _authenticatedExact, actualMember⟩ :=
      alignment.exactAt sample input k12 collisionFacts
    refine ⟨candidate, foldTrial, finalTrial, ?_⟩
    let coordinates := exactCandidateDirectedRegroupedCoordinates
      transitionFuel configuration candidate foldTrial finalTrial sample.1
        sample.2
    let factored := successfulGammaPrefixFactorization
      ⟨coordinates.2.2.2, success⟩
    let currentView := alignment.view candidate foldTrial finalTrial sample.1
      coordinates.1 coordinates.2.1 coordinates.2.2.1 factored.1
    change coordinates.2 ∈ foldFinalWorkQueryBatchDependentEvent
      (fun fold work skeleton =>
        (alignment.view candidate foldTrial finalTrial sample.1 coordinates.1
          fold work skeleton).target)
    refine ⟨foldAccepted, finalAccepted, success, ?_⟩
    change factored.2.1 ∈ currentView.target
    have factoredMember : factored.2.1 ∈ currentView.collisionTarget := by
      rw [← challengeExact]
      exact actualMember
    exact currentView.mem_target_of_active activeExact factoredMember

/-- Release-facing joint-batch bound from component-wise source alignment. -/
theorem exact_candidate_directed_joint_batch_probability_le_of_alignment
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
    (source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder)
    (alignment : ExactCandidateDirectedK13SourceAlignment transitionFuel
      configuration projection fixedInstance decoder source)
    (foldTrialCap : Fintype.card (ExactCompilerExposureTrial parameters) ≤
      2 ^ 31)
    (finalTrialCap : Fintype.card (ExactCompilerExposureTrial parameters) ≤
      2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactTag73K13JointQueryBatchCollisionEvent transitionFuel configuration
          projection fixedInstance decoder source) ≤
      candidateDirectedJointBatchRawError :=
  exact_candidate_directed_joint_batch_collision_probability_le hiddenLaw source
    alignment.toCausalSource foldTrialCap finalTrialCap

#print axioms ExactCandidateDirectedK13SourceAlignment
#print axioms ExactCandidateDirectedK13SourceAlignment.toCausalSource
#print axioms
  exact_candidate_directed_joint_batch_probability_le_of_alignment

end
end AspisK1.V7Tag73K13CandidateDirectedSourceBridge
