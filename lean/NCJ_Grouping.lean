import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
set_option autoImplicit false
namespace NCJ_Grouping
open scoped BigOperators
/-- Grouping preserves a weighted sum for ANY assignment of source indices
into groups. Applying this to the native table still needs its native-read law. -/
theorem contraction {R : Type} [CommSemiring R] {n m : Nat}
    (group : Fin n → Fin m) (a : Fin n → R) (weight : Fin m → R) :
    (∑ k : Fin m, (∑ j : Fin n with group j = k, a j) * weight k) =
      ∑ j : Fin n, a j * weight (group j) := by
  calc
    _ = ∑ k : Fin m, ∑ j : Fin n, if group j = k then a j * weight k else 0 := by
      simp only [Finset.sum_filter,Finset.sum_mul,ite_mul,zero_mul]
    _ = ∑ j : Fin n, ∑ k : Fin m, if group j = k then a j * weight k else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp

/-- The mask-subset calculation is linear in each coefficient, with no
restriction on overlapping masks or zero-mask groups. -/
theorem masks {R : Type} [CommSemiring R] {n m bits : Nat}
    (group : Fin n → Fin m) (mask : Fin m → Fin bits → Bool)
    (a : Fin n → R) (low : Fin bits → R) :
    (∑ k : Fin m, (∑ j : Fin n with group j=k, a j) *
      (∑ b : Fin bits, if mask k b then low b else 0)) =
      ∑ j : Fin n, ∑ b : Fin bits, if mask (group j) b then a j*low b else 0 := by
  rw [contraction]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.mul_sum,mul_ite,mul_zero]

#print axioms contraction
#print axioms masks
end NCJ_Grouping
