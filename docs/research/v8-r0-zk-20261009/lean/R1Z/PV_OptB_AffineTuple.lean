import R1Z.PV_OptB_CopySelection
set_option autoImplicit false
namespace R1Z.PV_OptB_AffineTuple
open R0P
variable {K : Type} [Field K]

def value (lam tag : K) (base : Fin 16 → K) (z : K) : K :=
  copyTupleValue lam (tag,fun j => if j = 0 then z else base j)

theorem affine (lam tag : K) (base : Fin 16 → K) (z : K) :
    value lam tag base z = value lam tag base 0 + lam*z := by
  unfold value copyTupleValue
  have summands :
      (fun j : Fin 16 => lam^(j.val+1) * (if j = 0 then z else base j)) =
      (fun j : Fin 16 => lam^(j.val+1) * (if j = 0 then 0 else base j) +
        (if j = 0 then lam*z else 0)) := by
    funext j
    by_cases zero : j = 0
    · subst j
      simp
    · simp only [zero,if_false,add_zero]
  rw [summands,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  exact (add_assoc _ _ _).symm

theorem injective (lam tag : K) (base : Fin 16 → K) (nonzero : lam ≠ 0) :
    Function.Injective (value lam tag base) := by
  intro a b same
  rw [affine lam tag base a,affine lam tag base b] at same
  exact mul_left_cancel₀ nonzero (add_left_cancel same)

#print axioms affine
#print axioms injective
end R1Z.PV_OptB_AffineTuple
