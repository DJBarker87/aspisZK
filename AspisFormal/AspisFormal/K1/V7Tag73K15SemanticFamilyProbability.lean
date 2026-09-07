import AspisFormal.K1.V7Tag73K15SemanticCandidateProbability

/-! Exact `30,500 / |QM31|` bound for the fixed width-29 family. -/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K15SemanticFamilyProbability

open MeasureTheory
open AspisK1.V7Tag73K15SemanticCandidateProbability
open AspisK1.V7Tag73K15SemanticSamplerFactorization
open AspisK1.V7Tag73K15SemanticValueProbability
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7FixedTupleSemanticSecurity
open AspisPool.V7FixedWidth29TupleList
open AspisPool.V7Width29ComponentExtraction
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound

noncomputable section

def fixedWidth29SemanticValueEvent
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (terminal : FixedWidth29TupleCandidate decoder lanes →
      FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder lanes →
      AdaptiveDegree27MessagePlan QM31Exact) :
    Set SemanticOrdinaryValueFamily :=
  ⋃ candidate : FixedWidth29TupleCandidate decoder lanes,
    fixedCandidateSemanticEvent (terminal candidate) (sumcheck candidate)

theorem fixedWidth29SemanticValueEvent_probability_le
    (decoder : ExactDecoderInstantiation QM31Exact)
    (lanes : Width29InitialWords QM31Exact)
    (terminal : FixedWidth29TupleCandidate decoder lanes →
      FixedTerminalAlgebraPlan QM31Exact)
    (sumcheck : FixedWidth29TupleCandidate decoder lanes →
      AdaptiveDegree27MessagePlan QM31Exact) :
    (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
        (fixedWidth29SemanticValueEvent decoder lanes terminal sumcheck) ≤
      (30500 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  unfold fixedWidth29SemanticValueEvent
  calc
    _ ≤ ∑ candidate : FixedWidth29TupleCandidate decoder lanes,
        (PMF.uniformOfFintype SemanticOrdinaryValueFamily).toOuterMeasure
          (fixedCandidateSemanticEvent (terminal candidate)
            (sumcheck candidate)) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _candidate : FixedWidth29TupleCandidate decoder lanes,
        (305 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
      exact Finset.sum_le_sum fun candidate _ ↦
        fixedCandidateSemanticEvent_probability_le
          (terminal candidate) (sumcheck candidate)
    _ = (Fintype.card (FixedWidth29TupleCandidate decoder lanes) : ENNReal) *
        ((305 : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) := by simp
    _ ≤ (100 : ENNReal) *
        ((305 : ENNReal) / ((P ^ 4 : Nat) : ENNReal)) := by
      gcongr
      exact_mod_cast fixedWidth29TupleCandidate_card_le_100 decoder lanes
    _ = (30500 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring

#print axioms fixedWidth29SemanticValueEvent_probability_le

end
end AspisK1.V7Tag73K15SemanticFamilyProbability
