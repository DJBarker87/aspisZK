import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisR1.F3M_SevenTerms
open scoped BigOperators

theorem split {K : Type*} [AddCommMonoid K] (f : Nat → K) :
    (∑ j ∈ Finset.range 7,f j)=f 0+∑ j : Fin 6,f (j.val+1) := by
  rw [Finset.sum_range_succ']
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j : Fin 6=>f (j.val+1))).symm

#print axioms split
end AspisR1.F3M_SevenTerms
