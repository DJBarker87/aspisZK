import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

/-! IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM. The V8 inverse-product cell is an ACTIVE
row. Overwriting it leaves inactive balancing intact, but discards a random
coordinate and inserts a witness-dependent value. Neither fact proves ZK. -/
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Privacy
variable {I F : Type*} [DecidableEq I]

def overwrite (t : I → F) (k : I) (value : F) : I → F :=
  fun i => if i = k then value else t i

theorem overwrite_ignores_old_coordinate (a b : I → F) (k : I) (value : F)
    (sameElsewhere : ∀ i, i ≠ k → a i = b i) :
    overwrite a k value = overwrite b k value := by
  funext i
  by_cases h : i = k
  · simp [overwrite, h]
  · simp [overwrite, h, sameElsewhere i h]

theorem overwrite_outside_sum [AddCommMonoid F]
    (inactive : Finset I) (k : I) (outside : k ∉ inactive) (t : I → F) (value : F) :
    (∑ i ∈ inactive, overwrite t k value i) = ∑ i ∈ inactive, t i := by
  apply Finset.sum_congr rfl
  intro i hi
  have ne : i ≠ k := by intro eq; subst i; exact outside hi
  simp [overwrite, ne]

/-- This equality is an algebraic balancing fact, NOT a privacy conclusion. -/
theorem overwrite_keeps_zero_sum [AddCommMonoid F]
    (inactive : Finset I) (k : I) (outside : k ∉ inactive) (t : I → F) (value : F)
    (balanced : (∑ i ∈ inactive, t i) = 0) :
    (∑ i ∈ inactive, overwrite t k value i) = 0 := by
  rw [overwrite_outside_sum inactive k outside t value, balanced]

#print axioms overwrite_ignores_old_coordinate
#print axioms overwrite_outside_sum
#print axioms overwrite_keeps_zero_sum
end AspisV8Privacy
