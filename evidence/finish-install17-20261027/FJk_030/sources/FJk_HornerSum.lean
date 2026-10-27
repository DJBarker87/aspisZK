import FIv_HornerAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_HornerSum
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)
/-- Symbolic coefficient sum; no concrete field or recurrence evaluation. -/
theorem value (theta : K) (xs : List NQ) :
    FIv_HornerAlgebra.low theta xs=
      ∑ i : Fin xs.length,theta^i.val*decode (xs[i.val]'i.isLt) := by
  induction xs with
  | nil => simp only [FIv_HornerAlgebra.low,List.length_nil,Finset.univ_eq_empty,Finset.sum_empty]
  | cons x xs ih =>
    rw [FIv_HornerAlgebra.low,ih]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,List.getElem_cons_zero,one_mul,Fin.val_succ,List.getElem_cons_succ]
    rw [Finset.mul_sum]
    apply congrArg (decode x+·)
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
#print axioms value
end AspisR1.FJk_HornerSum
end
