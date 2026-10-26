import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisR1.F3M_SevenTerms
open scoped BigOperators

theorem split {K : Type*} [AddCommMonoid K] (f : Nat → K) :
    (∑ j ∈ Finset.range 7,f j)=f 0+∑ j : Fin 6,f (j.val+1) := by
  rw [Fin.sum_univ_eq_sum_range,Finset.sum_range_succ']
  exact add_comm _ _

#print axioms split
end AspisR1.F3M_SevenTerms
