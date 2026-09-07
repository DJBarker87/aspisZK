import AspisFormal.K1.V7Tag73K15SemanticMuProbability
import AspisFormal.K1.V7Tag73K15SemanticSumcheckProbability

/-! Small type-independent union and arithmetic lemmas for semantic bounds. -/

set_option autoImplicit false

namespace AspisK1.V7Tag73K15SemanticUnionArithmetic

open MeasureTheory

theorem outerMeasure_three_union_iUnion_le
    {Tape : Type} (law : OuterMeasure Tape)
    (first second third : Set Tape) (roundEvent : Fin 10 → Set Tape) :
    law (first ∪ second ∪ third ∪ ⋃ round, roundEvent round) ≤
      law first + law second + law third + ∑ round, law (roundEvent round) := by
  have firstTwo := measure_union_le (μ := law) first second
  have firstThree := (measure_union_le (μ := law) (first ∪ second) third).trans
    (add_le_add_left firstTwo _)
  have allFour := (measure_union_le (μ := law)
    (first ∪ second ∪ third) (⋃ round, roundEvent round)).trans
      (add_le_add_left firstThree _)
  exact allFour.trans (add_le_add_right
    (measure_iUnion_fintype_le law roundEvent) _)

theorem semantic_cap_arithmetic (denominator : ENNReal) :
    (24 : ENNReal) / denominator + 10 / denominator + 1 / denominator +
        ∑ _round : Fin 10, 27 / denominator =
      305 / denominator := by
  simp [div_eq_mul_inv]
  ring

#print axioms outerMeasure_three_union_iUnion_le
#print axioms semantic_cap_arithmetic

end AspisK1.V7Tag73K15SemanticUnionArithmetic
