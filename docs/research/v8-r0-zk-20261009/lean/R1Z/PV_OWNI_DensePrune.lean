import Mathlib.Algebra.BigOperators.Group.Finset.Pi
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNI_DensePrune
open scoped BigOperators
variable {K : Type} [Field K]
/-- Symbolic prefix/suffix equality weight. No concrete Boolean cube reduces. -/
def weight {I : Type} [Fintype I] (p : I → K) (b : I → Bool) : K :=
 ∏ i,if b i then p i else 1-p i

theorem boolean_weight {I : Type} [Fintype I] [DecidableEq I] (s b : I → Bool) :
 weight (fun i=>if s i then (1:K) else 0) b=if b=s then 1 else 0 := by
 classical
 by_cases h:b=s
 · subst b
   rw [if_pos rfl]
   unfold weight
   apply Finset.prod_eq_one
   intro i hi
   cases hsi:s i <;> simp [hsi]
 · rw [if_neg h]
   obtain ⟨i,hi⟩:∃ i,b i≠s i:=Function.ne_iff.mp h
   apply Finset.prod_eq_zero (Finset.mem_univ i)
   cases hb:b i <;> cases hs:s i <;> simp_all

theorem dense_sparse {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
 (p : I → K) (suffix : J → Bool) (column : (I → Bool) → (J → Bool) → K) :
 (∑ a:I → Bool,∑ b:J → Bool,
  weight p a*weight (fun j=>if suffix j then (1:K) else 0) b*column a b)=
 ∑ a:I → Bool,weight p a*column a suffix := by
 classical
 apply Finset.sum_congr rfl
 intro a ha
 simp only [boolean_weight]
 simp
#print axioms boolean_weight
#print axioms dense_sparse
end R1Z.PV_OWNI_DensePrune
