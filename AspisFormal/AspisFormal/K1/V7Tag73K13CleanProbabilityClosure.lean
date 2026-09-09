import AspisFormal.K1.V7Tag73K13CleanCollisionSubset

/-! # Compiler-clean candidate-directed K1.3 measure bound -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CleanProbabilityClosure

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CandidateDirectedQueryBatchAccounting
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CleanCausalSource
open AspisK1.V7Tag73K13CleanCollisionSubset
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

theorem exact_clean_candidate_directed_joint_batch_collision_probability_le
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
    (causal : ExactCleanCandidateDirectedK13CausalSource transitionFuel
      configuration projection fixedInstance decoder source)
    (foldTrialCap : Fintype.card (ExactCompilerExposureTrial parameters) ≤
      2 ^ 31)
    (finalTrialCap : Fintype.card (ExactCompilerExposureTrial parameters) ≤
      2 ^ 34) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          exactTag73K13JointQueryBatchCollisionEvent transitionFuel configuration
            projection fixedInstance decoder source) ≤
      candidateDirectedJointBatchRawError := by
  let trials := causal.trials
  calc
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration
            projection fixedInstance ∩
          exactTag73K13JointQueryBatchCollisionEvent transitionFuel configuration
            projection fixedInstance decoder source) ≤
        (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          trials.failureUnion := by
      apply (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure.mono
      exact exact_clean_joint_batch_collision_subset_failure_union causal
    _ ≤ candidateDirectedJointBatchRawError :=
      trials.failure_probability_le foldTrialCap finalTrialCap

#print axioms
  exact_clean_candidate_directed_joint_batch_collision_probability_le

end
end AspisK1.V7Tag73K13CleanProbabilityClosure
