import NFQ_COMBINED_IMPORT
set_option autoImplicit false
namespace NFQ_Reduce
open Aeneas Aeneas.Std Result
/-- Model has the total reducer law; native packet retains its documented 2^62 domain. -/
theorem source (x : U64) :
    ∃ z, AspisR1SelectedMaskProbe.field.M31.reduce_u62 x=ok z ∧
      z.val=x.val%2147483647 ∧ z.val<2147483647 := by
  obtain ⟨z,run,value,canonical⟩ := AspisR1.ExtractedMaskReducer.current_reduce_mod x
  exact ⟨z,by simp only [AspisR1SelectedMaskProbe.field.M31.reduce_u62,run,bind_tc_ok],value,canonical⟩
#print axioms source
end NFQ_Reduce
