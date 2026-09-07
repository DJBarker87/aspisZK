import AspisFormal.K1.V7Tag73K15SemanticBasicProbability

/-! Exact probability bound for each adaptive semantic sumcheck round. -/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K15SemanticSumcheckProbability

open MeasureTheory
open AspisK1.V7Tag73K15SemanticBasicProbability
open AspisK1.V7Tag73K15SemanticSamplerFactorization
open AspisK1.V7Tag73K15SemanticValueProbability
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5ComponentCQM31TowerExact

noncomputable section

def fixedSumcheckRoundEvent
    (plan : AdaptiveDegree27MessagePlan QM31Exact) (round : Fin 10) :
    Set SemanticOrdinaryValueFamily :=
  {values | semanticSumcheckValue values round ∈
    plan.badAt (challengeHistory (semanticSumcheckValue values) round)}

/-- Reconstruct the earlier history without consulting the isolated current
coordinate. -/
def sumcheckHistoryFromResidual (round : Fin 10)
    (residual : SemanticSumcheckResidual round) : List QM31Exact :=
  List.ofFn fun earlier : Fin round.val ↦
    residual.2.2.2
      ⟨⟨earlier.val, lt_trans earlier.isLt round.isLt⟩, by
        intro equal
        have : earlier.val = round.val := congrArg Fin.val equal
        omega⟩

theorem sumcheckHistoryFromResidual_coordinates
    (round : Fin 10) (values : SemanticOrdinaryValueFamily) :
    sumcheckHistoryFromResidual round
        (semanticSumcheckValueCoordinates round values).1 =
      challengeHistory (semanticSumcheckValue values) round := by
  apply List.ext_get
  · simp [sumcheckHistoryFromResidual, challengeHistory]
  · intro index left right
    simp [sumcheckHistoryFromResidual, challengeHistory,
      semanticSumcheckValueCoordinates, splitSemanticSumcheckAt]

theorem fixedSumcheckRoundEvent_probability_le
    (plan : AdaptiveDegree27MessagePlan QM31Exact) (round : Fin 10) :
    (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
        (fixedSumcheckRoundEvent plan round) ≤
      (27 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply uniform_equiv_dependent_event_probability_le
    (semanticSumcheckValueCoordinates round)
    (fixedSumcheckRoundEvent plan round)
    {pair | pair.2 ∈ plan.badAt (sumcheckHistoryFromResidual round pair.1)}
  · intro values member
    change semanticSumcheckValue values round ∈
      plan.badAt (sumcheckHistoryFromResidual round
        (semanticSumcheckValueCoordinates round values).1)
    rw [sumcheckHistoryFromResidual_coordinates]
    exact member
  · intro residual
    change (PMF.uniformOfFintype QM31Exact).toOuterMeasure
      {value | value ∈ plan.badAt
        (sumcheckHistoryFromResidual round residual)} ≤ _
    exact uniform_qm31_finset_probability_le
      (plan.badAt (sumcheckHistoryFromResidual round residual)) 27
      (adaptiveDegree27_badAt_card_le plan
        (sumcheckHistoryFromResidual round residual))

#print axioms sumcheckHistoryFromResidual_coordinates
#print axioms fixedSumcheckRoundEvent_probability_le

end
end AspisK1.V7Tag73K15SemanticSumcheckProbability
