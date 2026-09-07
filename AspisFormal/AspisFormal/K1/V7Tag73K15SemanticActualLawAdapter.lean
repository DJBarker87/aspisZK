import AspisFormal.K1.V7Tag73K15SemanticSamplerFamilyProbability
import AspisFormal.K1.V7Tag73K15FixedActualLawAdapters

/-! Actual compiler-law adapter for the complete 22-sampler semantic family. -/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K15SemanticActualLawAdapter

open MeasureTheory
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73HiddenTapeAveraging
open AspisK1.V7Tag73K15SemanticFamilyProbability
open AspisK1.V7Tag73K15SemanticSamplerFactorization
open AspisK1.V7Tag73K15SemanticSamplerFamilyProbability
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7Width29ComponentExtraction
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound

noncomputable section

theorem exact_compiler_joint_law_semantic_family_probability_le
    {HiddenTape Residual : Type}
    [Fintype HiddenTape] [Fintype Residual] [Nonempty Residual]
    (hiddenLaw : PMF HiddenTape)
    (parameters : ExactCompilerResourceParameters)
    (coordinates : HiddenTape →
      FreshAnswerTape Digest256 (exactCompilerTargetCaps parameters).length ≃
        Residual × SemanticTotalTapeFamily)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : HiddenTape → Residual → SemanticOrdinarySkeletonFamily →
      Width29InitialWords QM31Exact)
    (terminal : ∀ hidden residual skeleton,
      FixedWidth29TupleCandidate decoder (lanes hidden residual skeleton) →
        FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : ∀ hidden residual skeleton,
      FixedWidth29TupleCandidate decoder (lanes hidden residual skeleton) →
        AdaptiveDegree27MessagePlan QM31Exact)
    (event : Set (ExactCompilerSample HiddenTape parameters))
    (covered : ∀ hidden, jointEventSlice event hidden ⊆
      coordinates hidden ⁻¹'
        dependentSuccessfulSubtypeEvent AllSemanticDuplexSamplersSucceed
          (fun residual ↦ successfulSemanticSamplerFamilyCoordinates ⁻¹'
            semanticSkeletonDependentEvent (fun skeleton ↦
              fixedWidth29SemanticValueEvent decoder
                (lanes hidden residual skeleton)
                (terminal hidden residual skeleton)
                (sumcheck hidden residual skeleton)))) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure event ≤
      (30500 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply joint_event_probability_le_of_every_slice_le hiddenLaw
    (exactCompilerTargetCaps parameters).length event
  intro hidden
  apply uniform_tape_dependent_successful_event_probability_le
    AllSemanticDuplexSamplersSucceed (coordinates hidden)
    successfulSemanticSamplerFamilyCoordinates
    (fun residual ↦ semanticSkeletonDependentEvent (fun skeleton ↦
      fixedWidth29SemanticValueEvent decoder
        (lanes hidden residual skeleton)
        (terminal hidden residual skeleton)
        (sumcheck hidden residual skeleton)))
    ((30500 : ENNReal) / ((P ^ 4 : Nat) : ENNReal))
  · intro residual
    exact semantic_fixed_width29_sampler_family_probability_le decoder
      (lanes hidden residual) (terminal hidden residual)
      (sumcheck hidden residual)
  · exact covered hidden

#print axioms exact_compiler_joint_law_semantic_family_probability_le

end
end AspisK1.V7Tag73K15SemanticActualLawAdapter
