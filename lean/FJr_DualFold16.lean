import FJr_Fin16Split
import FJg_DualTensor
import FJg_Permutation
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_DualFold16
open scoped BigOperators
variable {E : Type} [Field E]

theorem value (raw : Fin 1024 → E) (a0 a1 : E) (i : Fin 64) :
    RoundPairing.dualFold (n:=64) a1 (RoundPairing.dualFold (n:=256) a0 raw) i=
      ∑ u : Fin 16,(RoundPairing.quarter*RoundPairing.quarter)*
        (raw (childIndex (childIndex i ⟨u.val/4,by have:=u.isLt;omega⟩)
          ⟨u.val%4,Nat.mod_lt _ (by decide)⟩)*
          a0^FJc_LowModel.perm (u.val%4)*a1^FJc_LowModel.perm (u.val/4)) := by
  rw [FJr_Fin16Split.value]
  unfold RoundPairing.dualFold
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have mod4 : (4*s.val+t.val)%4=t.val := by have:=s.isLt;have:=t.isLt;omega
  have div4 : (4*s.val+t.val)/4=s.val := by have:=s.isLt;have:=t.isLt;omega
  simp only [mod4,div4,Fin.eta,FJg_Permutation.value]
  ring

#print axioms value
end AspisR1.FJr_DualFold16
end
