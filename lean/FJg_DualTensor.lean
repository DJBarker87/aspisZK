import FJg_TensorProduct
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_DualTensor
open scoped BigOperators
variable {E : Type} [Field E]

def low (f : Fin 4 → E) (a : E) : E :=
  RoundPairing.quarter * ∑ t : Fin 4,f t*a^((4-t.val)%4)

/-- Both model folds of the same tensor, with the original low lanes. -/
theorem value (f : Fin 5 → Fin 4 → E) (a0 a1 : E) (i : Fin 64) :
    RoundPairing.dualFold (n:=64) a1
      (RoundPairing.dualFold (n:=256) a0 (FJd_PointReference.tensor f)) i=
      low (f 0) a0*low (f 1) a1*FJg_TensorProduct.high f i := by
  unfold RoundPairing.dualFold
  simp_rw [FJg_TensorProduct.children,FJg_TensorProduct.value]
  unfold low
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  ring
#print axioms value
end AspisR1.FJg_DualTensor
end
