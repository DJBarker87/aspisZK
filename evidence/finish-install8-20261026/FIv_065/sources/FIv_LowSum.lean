import FIv_HornerAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_LowSum
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)
open scoped BigOperators

theorem value (theta : K) (xs : List NQ) :
    FIv_HornerAlgebra.low theta xs =
      ∑ j : Fin xs.length,theta^j.val*decode xs[j.val] := by
  induction xs with
  | nil => simp only [FIv_HornerAlgebra.low,Fin.sum_univ_zero]
  | cons x xs ih =>
    rw [FIv_HornerAlgebra.low,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,List.getElem_cons_zero,one_mul,
      Fin.val_succ,List.getElem_cons_succ]
    rw [ih,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring

#print axioms value
end AspisR1.FIv_LowSum
end
