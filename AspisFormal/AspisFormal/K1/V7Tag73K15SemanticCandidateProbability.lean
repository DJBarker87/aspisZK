import AspisFormal.K1.V7Tag73K15SemanticUnionArithmetic

/-! Exact `305 / |QM31|` probability bound for one fixed semantic plan. -/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K15SemanticCandidateProbability

open MeasureTheory
open AspisK1.V7Tag73K15SemanticBasicProbability
open AspisK1.V7Tag73K15SemanticMuProbability
open AspisK1.V7Tag73K15SemanticSamplerFactorization
open AspisK1.V7Tag73K15SemanticSumcheckProbability
open AspisK1.V7Tag73K15SemanticUnionArithmetic
open AspisK1.V7Tag73K15SemanticValueProbability
open AspisPool.V7FixedTupleSemanticSecurity
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound

noncomputable section

def fixedCandidateSemanticEvent
    (terminal : FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : AdaptiveDegree27MessagePlan QM31Exact) :
    Set SemanticOrdinaryValueFamily :=
  fixedThetaEvent terminal ∪ fixedPointEvent terminal ∪
    fixedMuEvent terminal ∪
      ⋃ round : Fin 10, fixedSumcheckRoundEvent sumcheck round

theorem fixedCandidateSemanticEvent_probability_le
    (terminal : FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : AdaptiveDegree27MessagePlan QM31Exact) :
    (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
        (fixedCandidateSemanticEvent terminal sumcheck) ≤
      (305 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  unfold fixedCandidateSemanticEvent
  calc
    _ ≤
        (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
            (fixedThetaEvent terminal) +
          (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
            (fixedPointEvent terminal) +
          (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
            (fixedMuEvent terminal) +
          ∑ round : Fin 10,
            (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
              (fixedSumcheckRoundEvent sumcheck round) := by
      exact outerMeasure_three_union_iUnion_le
        (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
        (fixedThetaEvent terminal) (fixedPointEvent terminal)
        (fixedMuEvent terminal) (fixedSumcheckRoundEvent sumcheck)
    _ ≤
        (24 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) +
          10 / ((P ^ 4 : Nat) : ENNReal) +
          1 / ((P ^ 4 : Nat) : ENNReal) +
          ∑ _round : Fin 10,
            27 / ((P ^ 4 : Nat) : ENNReal) := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (fixedThetaEvent_probability_le terminal)
            (fixedPointEvent_probability_le terminal))
          (fixedMuEvent_probability_le terminal))
        (Finset.sum_le_sum fun round _ ↦
          fixedSumcheckRoundEvent_probability_le sumcheck round)
    _ = (305 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) :=
      semantic_cap_arithmetic _

#print axioms fixedCandidateSemanticEvent_probability_le

end
end AspisK1.V7Tag73K15SemanticCandidateProbability
