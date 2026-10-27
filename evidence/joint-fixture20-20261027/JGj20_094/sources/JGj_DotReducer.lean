import FIv_Arithmetic
import ExtractedMaskReducer
set_option autoImplicit false
namespace AspisR1.JGj_DotReducer
open Aeneas Aeneas.Std Result FIq_Native
theorem source (x : U64) :
    ∃ out,field.M31.reduce_u64 x=ok out ∧ out.val<AspisV8R17.RawReducer.P := by
  obtain ⟨out,ro,_,co⟩ := ExtractedMaskReducer.current_wrapper_mod x
  exact ⟨out,(FIv_NativeArithmetic.m31_reduce x).trans ro,co⟩
#print axioms source
end AspisR1.JGj_DotReducer
