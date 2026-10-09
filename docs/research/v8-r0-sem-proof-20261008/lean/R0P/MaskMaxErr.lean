import R0P.SemMaxErr

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

#print axioms combinedD2BudgetWithEta_last
#print axioms combined_maxErrWithEta
#print axioms combined_maxErrWithEta_coefficient
end
end R0P.Mask
