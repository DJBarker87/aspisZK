import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact finite-sum regrouping for the retained S2 inactive contraction.
The concrete mask correspondence and emitted field/loop bindings are separate
obligations. This theorem imposes no nonzero-challenge assumption. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsGroups
open scoped BigOperators
variable {R : Type} [Semiring R] {n m k : Nat}

def grouped (group : Fin n → Fin m) (coefficient : Fin n → R) (weight : Fin m → R) : R :=
  ∑ g, (∑ j ∈ Finset.univ.filter (fun j => group j = g), coefficient j) * weight g

theorem grouped_eq_reference (group : Fin n → Fin m) (coefficient : Fin n → R)
    (weight : Fin m → R) :
    grouped group coefficient weight = ∑ j, coefficient j * weight (group j) := by
  unfold grouped
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ g, ∑ j ∈ Finset.univ.filter (fun j => group j = g), coefficient j * weight (group j) := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = _ := Finset.sum_fiberwise Finset.univ group (fun j => coefficient j * weight (group j))

def maskWeight (mask : Fin k → Bool) (low : Fin k → R) : R :=
  ∑ bit, if mask bit then low bit else 0

theorem grouped_mask_eq (group : Fin n → Fin m) (coefficient : Fin n → R)
    (mask : Fin m → Fin k → Bool) (inactive : Fin n → Fin k → Bool) (low : Fin k → R)
    (htable : ∀ j bit, mask (group j) bit = inactive j bit) :
    grouped group coefficient (fun g => maskWeight (mask g) low) =
      ∑ j, coefficient j * maskWeight (inactive j) low := by
  rw [grouped_eq_reference]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro bit _
  rw [htable j bit]

#print axioms grouped_eq_reference
#print axioms grouped_mask_eq
end AspisR1.CuSavingsGroups
