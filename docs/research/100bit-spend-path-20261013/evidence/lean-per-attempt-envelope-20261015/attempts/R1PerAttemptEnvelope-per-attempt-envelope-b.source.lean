import R1UnifiedQueryDensity
import R1SemanticBudget
import R1OpeningSamplerBound
import R1RhoSamplerBound
import R0C.SlackBits
import R0C.SlackObstruction

/-! Exact arithmetic facts for a common per-row rational envelope. These
inequalities do not state a Fiat--Shamir interpretation or a protocol-level
probability conclusion. -/
set_option autoImplicit false
namespace AspisR1.PerAttemptEnvelope

open AspisCircleGroupOrder

/-- The root-selected common numerical envelope. -/
def B : ℚ := 15 / (2^109 : ℚ)

theorem query_cap_le : UnifiedQueryDensity.queryCap ≤ B := by
  unfold UnifiedQueryDensity.queryCap B
  rw [R0C.SlackBits.bad_query_count, R0C.SlackObstruction.query_count]
  norm_num

private theorem semantic_roots_le (i : Fin 25) :
    SemanticBudget.roots i ≤ 217600 := by
  unfold SemanticBudget.roots
  split_ifs <;> omega

theorem semantic_row_le (i : Fin 25) :
    R0P.Mask.combinedD2BudgetZ i.val ≤ B := by
  rw [SemanticBudget.budget_eq i]
  have hr : (SemanticBudget.roots i : ℚ) ≤ 217600 := by
    exact_mod_cast semantic_roots_le i
  have ha : 0 ≤ SemanticBudget.atom := by
    unfold SemanticBudget.atom R0P.SemD2.deltaQ
    positivity
  calc
    (SemanticBudget.roots i : ℚ) * SemanticBudget.atom ≤
        (217600 : ℚ) * SemanticBudget.atom := mul_le_mul_of_nonneg_right hr ha
    _ ≤ B := by
      unfold B SemanticBudget.atom R0P.SemD2.deltaQ AspisCircleGroupOrder.P
      norm_num

theorem opening_cap_le : OpeningSamplerBound.openingCap ≤ B := by
  apply le_trans (le_of_lt OpeningSamplerBound.openingCap_lt_two_neg_199)
  unfold B
  norm_num

theorem rho_cap_le : RhoSamplerBound.rhoCap ≤ B := by
  apply le_trans (le_of_lt RhoSamplerBound.rhoCap_lt_two_neg_119)
  unfold B
  norm_num

theorem thirty_three_B_lt : (33 : ℚ) * B < 1 / (2^100 : ℚ) := by
  unfold B
  norm_num

#print axioms query_cap_le
#print axioms semantic_row_le
#print axioms opening_cap_le
#print axioms rho_cap_le
#print axioms thirty_three_B_lt

end AspisR1.PerAttemptEnvelope
