import FJi_WidePack
import FJi_Inputs
import FIp_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_PackCoefficient
open Aeneas Aeneas.Std
open FJi_Accumulations
/-- Pack the SAME eight selected coordinates back to the SAME coefficient. -/
theorem value (g : Array NE 29#usize) (n : Nat) :
    FJi_WidePack.pack (fun j=>(FJi_Inputs.coefficient g n j.val).val)=FIp_ArrayValue.value g n := by
  cases h : g.val[n]? with
  | none => simp only [FJi_Inputs.coefficient,FIp_ArrayValue.value,h];rfl
  | some x => simp only [FJi_Inputs.coefficient,FIp_ArrayValue.value,h];rfl
#print axioms value
end AspisR1.FJi_PackCoefficient
end
