import AspisFormal.K1.V7Tag73K15SemanticFamilyProbability
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningCore

/-! Transport the fixed semantic-family bound through all 22 successful samplers. -/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K15SemanticSamplerFamilyProbability

open MeasureTheory
open AspisK1.V7Tag73K15SemanticFamilyProbability
open AspisK1.V7Tag73K15SemanticSamplerFactorization
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisV5ComponentCQM31TowerExact

noncomputable section

def semanticSuccessfulAttemptFactorization :
    SemanticSuccessfulAttemptFamily ≃
      SemanticOrdinarySkeletonFamily × SemanticOrdinaryValueFamily :=
  successfulSemanticSamplerFamilyCoordinates.symm.trans
    successfulSemanticSamplerFactorization

def semanticSkeletonDependentEvent
    (target : SemanticOrdinarySkeletonFamily →
      Set SemanticOrdinaryValueFamily) :
    Set SemanticSuccessfulAttemptFamily :=
  semanticSuccessfulAttemptFactorization ⁻¹'
    {pair | pair.2 ∈ target pair.1}

theorem semantic_sampler_family_dependent_probability_le
    (target : SemanticOrdinarySkeletonFamily →
      Set SemanticOrdinaryValueFamily)
    (bound : ENNReal)
    (targetBound : ∀ skeleton,
      (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
          (target skeleton) ≤ bound) :
    (PMF.uniformOfFintype SemanticSuccessfulAttemptFamily).toOuterMeasure
        (semanticSkeletonDependentEvent target) ≤ bound := by
  calc
    _ = (PMF.uniformOfFintype
          (SemanticOrdinarySkeletonFamily ×
            SemanticOrdinaryValueFamily)).toOuterMeasure
          {pair | pair.2 ∈ target pair.1} := by
      calc
        _ = ((PMF.uniformOfFintype SemanticSuccessfulAttemptFamily).map
              semanticSuccessfulAttemptFactorization).toOuterMeasure
              {pair | pair.2 ∈ target pair.1} := by
            rw [PMF.toOuterMeasure_map_apply]
            rfl
        _ = _ := by
          rw [AspisV5RankOneOpeningHiding.uniform_map_equiv
            semanticSuccessfulAttemptFactorization]
    _ ≤ bound := by
      apply uniform_product_event_probability_le_of_every_slice_le
      intro skeleton
      change (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
        (target skeleton) ≤ bound
      exact targetBound skeleton

theorem semantic_fixed_width29_sampler_family_probability_le
    (decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      QM31Exact)
    (lanes : SemanticOrdinarySkeletonFamily →
      AspisPool.V7Width29ComponentExtraction.Width29InitialWords QM31Exact)
    (terminal : ∀ skeleton,
      AspisPool.V7FixedWidth29TupleList.FixedWidth29TupleCandidate decoder
          (lanes skeleton) →
        AspisV5SequentialTerminalChallengeBound.FixedTerminalAlgebraPlan
          QM31Exact)
    (sumcheck : ∀ skeleton,
      AspisPool.V7FixedWidth29TupleList.FixedWidth29TupleCandidate decoder
          (lanes skeleton) →
        AspisV5AdaptiveSumcheckChallengeBound.AdaptiveDegree27MessagePlan
          QM31Exact) :
    (PMF.uniformOfFintype SemanticSuccessfulAttemptFamily).toOuterMeasure
        (semanticSkeletonDependentEvent fun skeleton ↦
          fixedWidth29SemanticValueEvent decoder (lanes skeleton)
            (terminal skeleton) (sumcheck skeleton)) ≤
      (30500 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply semantic_sampler_family_dependent_probability_le
  intro skeleton
  exact fixedWidth29SemanticValueEvent_probability_le decoder
    (lanes skeleton) (terminal skeleton) (sumcheck skeleton)

#print axioms semantic_sampler_family_dependent_probability_le
#print axioms semantic_fixed_width29_sampler_family_probability_le

end
end AspisK1.V7Tag73K15SemanticSamplerFamilyProbability
