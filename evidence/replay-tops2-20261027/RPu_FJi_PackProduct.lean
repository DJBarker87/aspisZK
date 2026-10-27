import RPu_FJi_PackCoefficient
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_PackProduct
open Aeneas Aeneas.Std
open FJi_Accumulations
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (n : Nat) :
    FJi_WidePack.pack (fun j=>(FJi_Inputs.product q g slot j.val n : FJi_WidePack.F))=
      FIp_ArrayValue.value g n*FJi_WidePack.base (FJi_Inputs.scalar q slot (FJi_Inputs.cursor n)).val := by
  simp only [FJi_Inputs.product,Nat.cast_mul]
  rw [FJi_WidePack.scalar,FJi_PackCoefficient.value]
#print axioms value
end AspisR1.FJi_PackProduct
end
