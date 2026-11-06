import RPv_JFy_PreparedSteps
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ScalarStubLaw
open Aeneas Aeneas.Std Result WP
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
/-- Named full-Result discharge for NJX/NKI kind10 mul_m31 stubs, including
actual domain/length constants and233 reconstruction1024/1048576. -/
theorem source (x : NQ) (s : U32) :
 ∃ out,FIq_Native.field.QM31.mul_m31 x s=ok out ∧ Canon out ∧ decode out=decode x*(s.val : K) := by
 obtain ⟨out,call,hc⟩ := WP.spec_imp_exists (JFy_PreparedSteps.scalar x s)
 have value:=FIw_ScalarArithmetic.mul x out s call
 exact ⟨out,call,hc,value.2⟩
#print axioms source
end AspisR1.NKI_ScalarStubLaw
end
