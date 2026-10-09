import R0P.SemMaxErr
import R0P.MaskD2

/-! Accounting for inserting eta at row 14. The aggregate eta coefficient
is deliberately a parameter pending the lead's candidate-union decision. -/
set_option autoImplicit false
namespace R0P.Mask
open FS R0P.SemSource R0P.SemMaxErr R0C.SlackStatement AspisWideTower
noncomputable section

/-- Insert one eta budget, shifting the already degree-27 alpha rows and
all later rows. This is an accounting family, not a claim of masked D2. -/
def combinedD2BudgetWithEta (etaBudget : ℚ) (i : Nat) : ℚ :=
  if i < 14 then combinedD2Budget i
  else if i = 14 then etaBudget
  else combinedD2Budget (i - 1)

/-- The final query row is unchanged by insertion of eta. -/
theorem combinedD2BudgetWithEta_last (etaBudget : ℚ) :
    combinedD2BudgetWithEta etaBudget 31 = epsilonSlack WideExact delta0 4 := by
  simp only [combinedD2BudgetWithEta, if_neg (show ¬ (31 : Nat) < 14 by omega),
    if_neg (show ¬ (31 : Nat) = 14 by omega), Nat.reduceSub,
    combinedD2Budget, dif_neg (show ¬ (30 : Nat) < 24 by omega),
    if_neg (show ¬ (30 : Nat) < 26 by omega),
    if_neg (show ¬ (30 : Nat) < 30 by omega)]

/-- Any inserted eta budget below the query row preserves the exact maximum. -/
theorem combined_maxErrWithEta (etaBudget : ℚ)
    (hEta : etaBudget ≤ epsilonSlack WideExact delta0 4) :
    maxErr (combinedD2BudgetWithEta etaBudget) 32 = epsilonSlack WideExact delta0 4 := by
  rw [← combinedD2BudgetWithEta_last etaBudget]
  apply maxErr_eq_of_le _ _ 31 (by omega)
  · rw [combinedD2BudgetWithEta_last]
    exact query_nonneg
  · intro i _
    rw [combinedD2BudgetWithEta_last]
    unfold combinedD2BudgetWithEta
    split_ifs
    · exact combined_row_le_query i
    · exact hEta
    · exact combined_row_le_query (i - 1)

/-- Both coefficient 1 and coefficient 100 fall within this proved range. -/
theorem combined_maxErrWithEta_coefficient (c : ℚ) (hc0 : 0 ≤ c) (hc : c ≤ 217600) :
    maxErr (combinedD2BudgetWithEta ((1 + deltaQ) * c /
      (AspisCircleGroupOrder.P : ℚ)^4)) 32 = epsilonSlack WideExact delta0 4 :=
  combined_maxErrWithEta _ (small_budget_le_query c hc0 hc)

/-- The two circle rows use the larger authorized 2/P^4 envelope. -/
theorem masked_circle_le_query :
    2 / (AspisCircleGroupOrder.P : ℚ)^4 ≤ epsilonSlack WideExact delta0 4 := by
  apply le_trans _ (small_budget_le_query 2 (by norm_num) (by norm_num))
  apply div_le_div_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg _) _)
  have hδ := deltaQ_nonneg
  linarith

theorem combined_rowZ_le_query (i : Nat) :
    combinedD2BudgetZ i ≤ epsilonSlack WideExact delta0 4 := by
  unfold combinedD2BudgetZ
  split_ifs with h14 heq h25 h27 h31
  · exact combined_row_le_query i
  · have h := small_budget_le_query 100 (by norm_num) (by norm_num)
    convert h using 1
    ring
  · simpa only [mul_div_assoc] using small_budget_le_query 2700 (by norm_num) (by norm_num)
  · exact masked_circle_le_query
  · exact opening_le_query (i - 27) (by omega)
  · exact le_rfl

/-- The final q22 row attains the maximum for the fixed masked budget. -/
theorem combined_maxErrZ :
    maxErr combinedD2BudgetZ 32 = epsilonSlack WideExact delta0 4 := by
  have hlast : combinedD2BudgetZ 31 = epsilonSlack WideExact delta0 4 := by
    simp only [combinedD2BudgetZ, if_neg (show ¬ (31 : Nat) < 14 by omega),
      if_neg (show ¬ (31 : Nat) = 14 by omega),
      if_neg (show ¬ (31 : Nat) < 25 by omega),
      if_neg (show ¬ (31 : Nat) < 27 by omega),
      if_neg (show ¬ (31 : Nat) < 31 by omega)]
  rw [← hlast]
  apply maxErr_eq_of_le _ _ 31 (by omega)
  · rw [hlast]; exact query_nonneg
  · intro i _
    rw [hlast]
    exact combined_rowZ_le_query i

#print axioms masked_circle_le_query
#print axioms combined_rowZ_le_query
#print axioms combined_maxErrZ

#print axioms combinedD2BudgetWithEta_last
#print axioms combined_maxErrWithEta
#print axioms combined_maxErrWithEta_coefficient
end
end R0P.Mask
