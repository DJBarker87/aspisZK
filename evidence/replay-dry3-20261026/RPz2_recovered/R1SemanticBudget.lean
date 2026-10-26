import R0P.MaskDensity

/-! Exact accounting for the unchanged 25-row semantic prefix. This is the
sum of prefix-conditional independent-answer bounds, not a Fiat--Shamir or
adaptive shared-oracle security theorem. No work/grinding factor appears. -/
set_option autoImplicit false
namespace AspisR1.SemanticBudget
open R0P R0P.Mask R0P.SemSource R0P.SemD3Glue R0P.SemRounds
open AspisCircleGroupOrder
open scoped BigOperators

/-- Candidate-unioned root caps, in their actual challenge order. -/
def roots (i : Fin 25) : Nat :=
  if i.val = 0 then 217600 else if i.val = 1 then 54400 else
  if i.val = 2 then 2800 else if i.val < 13 then 100 else
  if i.val = 13 then 200 else if i.val = 14 then 100 else 2700

def atom : ℚ := (1 + deltaQ) / (P : ℚ)^4

theorem budget_eq (i : Fin 25) :
    combinedD2BudgetZ i.val = (roots i : ℚ) * atom := by
  unfold combinedD2BudgetZ combinedD2Budget semRoundBudget roots atom
  split_ifs <;> norm_num at *
  all_goals first | omega | ring

/-- Only 25 small scalar entries are evaluated here, not a generated
recurrence or a finite-field/candidate enumeration. -/
theorem roots_sum : ∑ i : Fin 25, roots i = 303100 := by
  norm_num [Fin.sum_univ_succ, roots]

theorem budget_sum : ∑ i : Fin 25, combinedD2BudgetZ i.val = 303100 * atom := by
  simp_rw [budget_eq]
  rw [← Finset.sum_mul, ← Nat.cast_sum, roots_sum]
  norm_num

#print axioms budget_eq
#print axioms roots_sum
#print axioms budget_sum
end AspisR1.SemanticBudget
