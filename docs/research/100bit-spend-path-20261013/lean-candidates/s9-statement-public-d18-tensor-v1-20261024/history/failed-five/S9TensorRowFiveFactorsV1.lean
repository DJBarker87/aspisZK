import S9StatementTensorGenericV1
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace AspisR1S9TensorRowFiveFactorsV1
open AspisR1S9StatementTensorGenericV1
variable {K : Type} [Field K]

/-- Exact five-factor source grouping. All factors and the index remain
symbolic; the finite product has five opaque entries, never1024cells. -/
theorem tensorRow_eq_five_factors (row : Nat → Nat → K) (j : Fin 1024) :
    tensorRow row j=
      (row 0 (j.val%4)*row 1 ((j.val/4)%4))*
        ((row 2 ((j.val/16)%4)*row 3 (((j.val/16)/4)%4))*row 4 ((j.val/16)/16)) := by
  unfold tensorRow
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,Fin.val_zero,Fin.val_succ,
    Nat.zero_add,Nat.div_one,mul_one]
  norm_num only
  have h64 : j.val/16/4=j.val/64 := by omega
  have h256 : j.val/16/16=j.val/256 := by omega
  have hlast : j.val/256<4 := by have := j.isLt; omega
  rw [h64,h256,Nat.mod_eq_of_lt hlast]
  ring

#print axioms tensorRow_eq_five_factors
end AspisR1S9TensorRowFiveFactorsV1
end
