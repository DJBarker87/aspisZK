import AspisFormal.K1.V7Tag73CausalFoldFinalWorkQueryBatchProbability
import AspisFormal.K1.V7Tag73ExactConcreteK13K14Events
import AspisFormal.K1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting

/-!
# Candidate-directed K1.3 actual-law probability closure

The remaining source obligation is deterministic: map each concrete deployed
joint-batch collision to one member of the exact 542-coordinate finite family.
No probability inequality is a premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CandidateDirectedProbabilityClosure

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
open AspisK1.V7Tag73ExactFoldArmedCandidateQueryBatchRootRouting
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkDigestProbability
open AspisK1.V7Tag73JointQueryBatchSoundness
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

def exactCandidateDirectedRegroupedCoordinates
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (candidate : Q16DigestSlot)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
        (AlphaZeroDigestBlocks × Q16CandidateDigestForest)) ×
      (Digest256 × (Digest256 × TotalGammaDuplexTape)) :=
  let router := exactCompilerFoldArmedCandidateQueryBatchRouter parameters
    transitionFuel foldTrial.val finalTrial.val candidate
    (exactPlainRomCursor configuration hidden).erase
  foldFinalWorkQueryBatchCoordinateRegroup
      (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters)
      AlphaZeroDigestBlocks Q16CandidateDigestForest
    (exactCompilerCausalFoldAlphaFinalWorkQ16QueryBatchCoordinates parameters
      router tape)

/-- Exact deterministic production/source bridge still required by K1.3.
It names the finite target before the query-batch answer and maps every
concrete collision witness to one candidate/fold/final causal coordinate. -/
structure ExactCandidateDirectedK13CausalSource
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
  target : Q16DigestSlot →
    ExactCompilerExposureTrial parameters →
    ExactCompilerExposureTrial parameters → HiddenTape →
    (ExactCompilerFoldAlphaFinalWorkQ16QueryBatchResidual parameters ×
      (AlphaZeroDigestBlocks × Q16CandidateDigestForest)) →
    Digest256 → Digest256 → VariableGammaCompleteSkeleton →
      Finset QM31Exact
  targetCard : ∀ candidate foldTrial finalTrial hidden context fold work
      skeleton,
    (target candidate foldTrial finalTrial hidden context fold work
      skeleton).card ≤ 16
  collisionMapped : ∀
      (sample : ExactCompilerSample HiddenTape parameters)
      (input : ExactK12OperationalInput transitionFuel configuration projection
        fixedInstance sample)
      (k12 : ExactPrefixK12Certificate input),
    exactTag73K13ExpectedQueryVector decoder input k12 ≠
        exactTag73K13AuthenticatedQueryVector decoder input k12 ∧
      exactOperationalChallenge input .queryBatch ∈
        exactTag73JointQueryBatchNonzeroCollisionSet
          (source.preQueryDiscrepancy sample input)
          (exactTag73K13ExpectedQueryVector decoder input k12)
          (exactTag73K13AuthenticatedQueryVector decoder input k12) →
    ∃ candidate foldTrial finalTrial,
      let coordinates := exactCandidateDirectedRegroupedCoordinates
        transitionFuel configuration candidate foldTrial finalTrial sample.1
          sample.2
      coordinates.2 ∈ foldFinalWorkQueryBatchDependentEvent
        (target candidate foldTrial finalTrial sample.1 coordinates.1)

noncomputable def exactCandidateDirectedQueryBatchTrials
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
      projection fixedInstance decoder)
    (causal : ExactCandidateDirectedK13CausalSource transitionFuel configuration
      projection fixedInstance decoder source) :
    ExactCompilerCandidateDirectedQueryBatchTrials
      (HiddenTape := HiddenTape)
      (FoldTrial := ExactCompilerExposureTrial parameters)
      (FinalTrial := ExactCompilerExposureTrial parameters) parameters where
  event := fun candidate foldTrial finalTrial sample =>
    let coordinates := exactCandidateDirectedRegroupedCoordinates
      transitionFuel configuration candidate foldTrial finalTrial sample.1
        sample.2
    coordinates.2 ∈ foldFinalWorkQueryBatchDependentEvent
      (causal.target candidate foldTrial finalTrial sample.1 coordinates.1)
  router := fun candidate foldTrial finalTrial hidden =>
    exactCompilerFoldArmedCandidateQueryBatchRouter parameters transitionFuel
      foldTrial.val finalTrial.val candidate
      (exactPlainRomCursor configuration hidden).erase
  target := causal.target
  targetCard := causal.targetCard
  covered := by
    intro candidate foldTrial finalTrial hidden tape member
    exact member

theorem exact_joint_batch_collision_subset_candidate_directed_failure_union
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
    (causal : ExactCandidateDirectedK13CausalSource transitionFuel configuration
      projection fixedInstance decoder source) :
    exactTag73K13JointQueryBatchCollisionEvent transitionFuel configuration
        projection fixedInstance decoder source ⊆
      (exactCandidateDirectedQueryBatchTrials transitionFuel configuration
        projection fixedInstance decoder source causal).failureUnion := by
  intro sample member
  rcases member with ⟨input, k12, collisionFacts⟩
  obtain ⟨candidate, foldTrial, finalTrial, mapped⟩ :=
    causal.collisionMapped sample input k12 collisionFacts
  apply Set.mem_iUnion.mpr
  refine ⟨candidate, Set.mem_iUnion.mpr ⟨foldTrial,
    Set.mem_iUnion.mpr ⟨finalTrial, ?_⟩⟩⟩
  exact mapped

theorem exact_candidate_directed_joint_batch_collision_probability_le
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
    (causal : ExactCandidateDirectedK13CausalSource transitionFuel configuration
      projection fixedInstance decoder source)
    (foldTrialCap : Fintype.card (ExactCompilerExposureTrial parameters) ≤
      2 ^ 31)
    (finalTrialCap : Fintype.card (ExactCompilerExposureTrial parameters) ≤
      2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactTag73K13JointQueryBatchCollisionEvent transitionFuel configuration
          projection fixedInstance decoder source) ≤
      candidateDirectedJointBatchRawError := by
  let trials := exactCandidateDirectedQueryBatchTrials transitionFuel
    configuration projection fixedInstance decoder source causal
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactTag73K13JointQueryBatchCollisionEvent transitionFuel configuration
          projection fixedInstance decoder source) ≤
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          trials.failureUnion := by
      apply (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
      exact exact_joint_batch_collision_subset_candidate_directed_failure_union
        causal
    _ ≤ candidateDirectedJointBatchRawError :=
      trials.failure_probability_le foldTrialCap finalTrialCap

#print axioms ExactCandidateDirectedK13CausalSource
#print axioms exactCandidateDirectedQueryBatchTrials
#print axioms exact_joint_batch_collision_subset_candidate_directed_failure_union
#print axioms exact_candidate_directed_joint_batch_collision_probability_le

end
end AspisK1.V7Tag73K13CandidateDirectedProbabilityClosure
