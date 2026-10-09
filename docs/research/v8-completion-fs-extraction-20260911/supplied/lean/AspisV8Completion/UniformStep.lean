/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import AspisV8Completion.AdaptiveHazard
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.UniformStep
noncomputable section
variable {A : Type*} [Fintype A] [Nonempty A]

/-- Full answer space, not a distribution conditioned on observed success. -/
def weight (_a : A) : ℚ := 1/(Fintype.card A : ℚ)

theorem weight_nonneg (a : A) : 0 ≤ weight a := by
  unfold weight
  positivity

theorem weight_total : (∑ a : A, weight a) = 1 := by
  have positive : 0 < Fintype.card A := Fintype.card_pos
  have nonzero : (Fintype.card A : ℚ) ≠ 0 := by positivity
  simp [weight, nonzero]

def badSet (hit : A → Bool) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => hit a = true)

theorem hit_mass (hit : A → Bool) :
    (∑ a, weight a*(if hit a then (1:ℚ) else 0)) =
      (badSet hit).card/(Fintype.card A : ℚ) := by
  classical
  have filtered : (∑ a, weight a*(if hit a then (1:ℚ) else 0)) =
      ∑ a ∈ badSet hit, weight a := by
    simp only [badSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    cases h : hit a <;> simp [h]
  rw [filtered]
  simp [weight, div_eq_mul_inv]

theorem hit_mass_bound (hit : A → Bool) (m : Nat) (cap : (badSet hit).card ≤ m) :
    (∑ a, weight a*(if hit a then (1:ℚ) else 0)) ≤ m/(Fintype.card A : ℚ) := by
  rw [hit_mass]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr cap) (Nat.cast_nonneg _)

#print axioms weight_total
#print axioms hit_mass_bound
end
end AspisV8Completion.UniformStep
