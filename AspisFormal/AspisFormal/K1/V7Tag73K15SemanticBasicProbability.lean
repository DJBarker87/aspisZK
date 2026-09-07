import AspisFormal.K1.V7Tag73K15SemanticZerocheckProbability

/-! Exact theta, zerocheck-point, and helper-mu probability bounds. -/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K15SemanticBasicProbability

open MeasureTheory
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73K15SemanticSamplerFactorization
open AspisK1.V7Tag73K15SemanticValueProbability
open AspisK1.V7Tag73K15SemanticZerocheckProbability
open AspisPool.V7FixedTupleSemanticSecurity
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound

noncomputable section

theorem uniform_qm31_finset_probability_le
    (target : Finset QM31Exact) (cap : Nat)
    (cardBound : target.card ≤ cap) :
    (PMF.uniformOfFintype QM31Exact).toOuterMeasure
        {value | value ∈ target} ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  rw [uniform_ordinary_target_probability_exact]
  gcongr

def fixedThetaEvent (plan : FixedTerminalAlgebraPlan QM31Exact) :
    Set SemanticOrdinaryValueFamily :=
  {values | semanticThetaValue values ∈ plan.thetaBad}

def fixedPointEvent (plan : FixedTerminalAlgebraPlan QM31Exact) :
    Set SemanticOrdinaryValueFamily :=
  {values | semanticPointValue values ∈
    plan.pointBad (semanticThetaValue values)}

theorem fixedThetaEvent_probability_le
    (plan : FixedTerminalAlgebraPlan QM31Exact) :
    (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
        (fixedThetaEvent plan) ≤
      (24 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply uniform_equiv_dependent_event_probability_le
    semanticThetaValueCoordinates (fixedThetaEvent plan)
    {pair | pair.2 ∈ plan.thetaBad} (by intro values member; exact member)
  intro residual
  change (PMF.uniformOfFintype QM31Exact).toOuterMeasure
      {value | value ∈ plan.thetaBad} ≤ _
  exact uniform_qm31_finset_probability_le plan.thetaBad 24
    (fixedTerminal_thetaBad_card_le_twenty_four plan)

theorem fixedPointEvent_probability_le
    (plan : FixedTerminalAlgebraPlan QM31Exact) :
    (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
        (fixedPointEvent plan) ≤
      (10 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply uniform_equiv_dependent_event_probability_le
    semanticPointValueCoordinates (fixedPointEvent plan)
    {pair | pair.2 ∈ plan.pointBad pair.1.1}
    (by intro values member; exact member)
  intro residual
  change (PMF.uniformOfFintype SemanticPointValues).toOuterMeasure
      (↑(plan.pointBad residual.1) : Set SemanticPointValues) ≤ _
  exact uniform_pointBad_probability_le_ten plan residual.1

#print axioms uniform_qm31_finset_probability_le
#print axioms fixedThetaEvent_probability_le
#print axioms fixedPointEvent_probability_le

end
end AspisK1.V7Tag73K15SemanticBasicProbability
