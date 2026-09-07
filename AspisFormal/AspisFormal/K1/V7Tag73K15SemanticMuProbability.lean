import AspisFormal.K1.V7Tag73K15SemanticBasicProbability

/-! Exact helper-mu probability bound, isolated for bounded elaboration. -/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K15SemanticMuProbability

open MeasureTheory
open AspisK1.V7Tag73K15SemanticBasicProbability
open AspisK1.V7Tag73K15SemanticSamplerFactorization
open AspisK1.V7Tag73K15SemanticValueProbability
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound

noncomputable section

def semanticMuDependentEvent
    (target : SemanticMuResidual → Finset QM31Exact) :
    Set SemanticOrdinaryValueFamily :=
  {values | (semanticMuValueCoordinates values).2 ∈
    target (semanticMuValueCoordinates values).1}

theorem semanticMuDependentEvent_probability_le
    (target : SemanticMuResidual → Finset QM31Exact)
    (cap : Nat) (targetCap : ∀ residual, (target residual).card ≤ cap) :
    (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
        (semanticMuDependentEvent target) ≤
      (cap : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  apply uniform_equiv_dependent_event_probability_le
    semanticMuValueCoordinates (semanticMuDependentEvent target)
    {pair | pair.2 ∈ target pair.1} (by intro values member; exact member)
  intro residual
  change (PMF.uniformOfFintype QM31Exact).toOuterMeasure
      {value | value ∈ target residual} ≤ _
  exact uniform_qm31_finset_probability_le
    (target residual) cap (targetCap residual)

def fixedMuTarget (plan : FixedTerminalAlgebraPlan QM31Exact)
    (residual : SemanticMuResidual) : Finset QM31Exact :=
  plan.muBad residual.1 residual.2.1

def fixedMuEvent (plan : FixedTerminalAlgebraPlan QM31Exact) :
    Set SemanticOrdinaryValueFamily :=
  semanticMuDependentEvent (fixedMuTarget plan)

theorem fixedMuEvent_probability_le
    (plan : FixedTerminalAlgebraPlan QM31Exact) :
    (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
        (fixedMuEvent plan) ≤
      (1 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  have bound := semanticMuDependentEvent_probability_le
    (fixedMuTarget plan) 1 (fun residual ↦
      fixedTerminal_muBad_card_le_one plan residual.1 residual.2.1)
  simpa only [fixedMuEvent, Nat.cast_one] using bound

end
end AspisK1.V7Tag73K15SemanticMuProbability
