import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
open scoped BigOperators
namespace AspisV8R12
variable {K U V I : Type*} [Field K]
variable [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]

theorem pair_in_kernel (L : U →ₗ[K] V) (left right : U)
    (same : L left = L right) : L (left-right) = 0 := by
  simp [same]

theorem sum_pairs_in_kernel (is : Finset I) (L : U →ₗ[K] V)
    (left right : I → U) (same : ∀ i ∈ is, L (left i) = L (right i)) :
    L (∑ i ∈ is, (left i-right i)) = 0 := by
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact pair_in_kernel L (left i) (right i) (same i hi)

theorem correction_preserves_previous (L : U →ₗ[K] V) (g delta : U)
    (zero : L delta = 0) : L (g+delta) = L g := by
  simp [zero]

#print axioms pair_in_kernel
#print axioms sum_pairs_in_kernel
#print axioms correction_preserves_previous
end AspisV8R12
