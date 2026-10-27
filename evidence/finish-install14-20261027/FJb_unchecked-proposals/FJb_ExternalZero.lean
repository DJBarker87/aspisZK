import FJb_ExternalExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_ExternalZero
open FIv_NativeValue (K)
/-- Local model witnesses only;no full accepted execution is asserted. -/
theorem mat4 : R0P.poseidonMat4 (fun _ : Fin 4=>(0 : K))=(fun _=>0) := by
  funext i
  fin_cases i <;> simp [R0P.poseidonMat4]

theorem value : R0P.poseidonExternalLinear (fun _ : Fin 16=>(0 : K))=(fun _=>0) := by
  funext i
  simp only [R0P.poseidonExternalLinear,mat4,zero_add]
#print axioms mat4
#print axioms value
end AspisR1.FJb_ExternalZero
end
