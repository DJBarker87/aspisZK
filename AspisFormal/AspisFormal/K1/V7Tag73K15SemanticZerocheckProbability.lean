import AspisFormal.K1.V7Tag73K15SemanticValueProbability

/-!
# Exact zerocheck-point probability for one fixed semantic plan

This small module is separated deliberately: elaborating the ten-coordinate
cardinality cast in the larger value-coordinate module overflowed Lean's
process stack even though memory usage was modest.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K15SemanticZerocheckProbability

open MeasureTheory
open AspisK1.V7Tag73K15SemanticValueProbability
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound

noncomputable section

/-- Uniform probability of one fixed zerocheck point target. -/
theorem uniform_pointBad_probability_le_ten
    (plan : FixedTerminalAlgebraPlan QM31Exact) (theta : QM31Exact) :
    (PMF.uniformOfFintype SemanticPointValues).toOuterMeasure
        (↑(plan.pointBad theta) : Set SemanticPointValues) ≤
      (10 : ENNReal) / ((P ^ 4 : Nat) : ENNReal) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have cardSubtype :
      Fintype.card ↥(↑(plan.pointBad theta) : Set SemanticPointValues) =
        (plan.pointBad theta).card := by
    let equivalence :
        ↥(↑(plan.pointBad theta) : Set SemanticPointValues) ≃
          ↥(plan.pointBad theta) :=
      { toFun := fun point ↦ ⟨point.1, point.2⟩
        invFun := fun point ↦ ⟨point.1, point.2⟩
        left_inv := by intro point; cases point; rfl
        right_inv := by intro point; cases point; rfl }
    exact (Fintype.card_congr equivalence).trans (Fintype.card_coe _)
  rw [cardSubtype]
  rw [show Fintype.card SemanticPointValues = (P ^ 4 : Nat) ^ 10 by
    simp [SemanticPointValues, qm31Exact_card]]
  by_cases tableNonzero :
      thetaConstraintTable plan.basis plan.constraintRows theta ≠ 0
  · rw [FixedTerminalAlgebraPlan.pointBad, if_pos tableNonzero]
    let table := thetaConstraintTable plan.basis plan.constraintRows theta
    let lhs : ℚ≥0 :=
      ((zerocheckCollisionSet table).card : ℚ≥0) /
        (Fintype.card QM31Exact ^ 10)
    let rhs : ℚ≥0 := (10 : ℚ≥0) / Fintype.card QM31Exact
    have nnratBound : lhs ≤ rhs :=
      uniform_zerocheck_collision_fraction_le_ten table tableNonzero
    have nnrealBound : (lhs : NNReal) ≤ (rhs : NNReal) :=
      (NNRat.cast_le (K := NNReal)).2 nnratBound
    dsimp only [lhs, rhs] at nnrealBound
    simp only [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_pow] at nnrealBound
    have cardNe : (Fintype.card QM31Exact : NNReal) ≠ 0 := by
      positivity
    have cardPowNe : (Fintype.card QM31Exact : NNReal) ^ 10 ≠ 0 :=
      pow_ne_zero _ cardNe
    have nnrealBound' :
        (((zerocheckCollisionSet table).card : NNReal) /
            (Fintype.card QM31Exact : NNReal) ^ 10 : NNReal) ≤
          ((10 : NNReal) / (Fintype.card QM31Exact : NNReal) : NNReal) :=
      nnrealBound
    have ennrealBound' :
        ENNReal.ofNNReal
            (((zerocheckCollisionSet table).card : NNReal) /
              (Fintype.card QM31Exact : NNReal) ^ 10) ≤
          ENNReal.ofNNReal
            ((10 : NNReal) / (Fintype.card QM31Exact : NNReal)) :=
      ENNReal.coe_le_coe.2 nnrealBound'
    rw [
      ENNReal.coe_div cardPowNe, ENNReal.coe_div cardNe,
      ENNReal.coe_pow] at ennrealBound'
    rw [ENNReal.coe_natCast (zerocheckCollisionSet table).card,
      ENNReal.coe_natCast (Fintype.card QM31Exact)] at ennrealBound'
    rw [ENNReal.coe_ofNat 10] at ennrealBound'
    simpa only [table, qm31Exact_card, Nat.cast_pow] using ennrealBound'
  · simp [FixedTerminalAlgebraPlan.pointBad, tableNonzero]

#print axioms uniform_pointBad_probability_le_ten

end

end AspisK1.V7Tag73K15SemanticZerocheckProbability
