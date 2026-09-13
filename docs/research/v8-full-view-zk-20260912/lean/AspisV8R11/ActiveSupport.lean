import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

set_option autoImplicit false
open scoped BigOperators
namespace AspisV8R11
variable {Row K : Type*} [DecidableEq Row] [AddCommGroup K]

theorem inactive_sum_preserved
    (inactive : Finset Row) (g delta : Row → K)
    (support : ∀ r ∈ inactive, delta r = 0) :
    (∑ r ∈ inactive, (g r + delta r)) = ∑ r ∈ inactive, g r := by
  apply Finset.sum_congr rfl
  intro r hr
  simp [support r hr]

theorem active_correction_preserves_balance
    (inactive : Finset Row) (g delta : Row → K)
    (support : ∀ r ∈ inactive, delta r = 0)
    (balanced : (∑ r ∈ inactive, g r) = 0) :
    (∑ r ∈ inactive, (g r + delta r)) = 0 := by
  rw [inactive_sum_preserved inactive g delta support, balanced]

#print axioms inactive_sum_preserved
#print axioms active_correction_preserves_balance
end AspisV8R11
