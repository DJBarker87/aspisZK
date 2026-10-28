import RPv_FJb_M31Scalar
import RPv_JFy_Pow5
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_M31ScalarTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
theorem source (x : NQ) (c : U32) (hx : Canon x) (hc : c.val<FJb_M31Scalar.P) :
    ∃ m out,field.M31.add x.c0.a c=ok m ∧
      state_only_poseidon.pow5 (FJb_M31Scalar.updated x m)=ok out ∧ Canon out := by
  obtain ⟨m,hm,_,cm⟩ := ExtractedMaskM31AddSub.current_add_mod x.c0.a c hx.1.1 hc
  have rm := (FIv_NativeArithmetic.m31_add x.c0.a c).trans hm
  have cu : Canon (FJb_M31Scalar.updated x m) := ⟨⟨cm,hx.1.2⟩,hx.2⟩
  obtain ⟨out,ro,co,_⟩ := JFy_Pow5.source _ cu
  exact ⟨m,out,rm,ro,co⟩
#print axioms source
end AspisR1.JGj_M31ScalarTotal
end
