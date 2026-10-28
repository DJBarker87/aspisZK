import LPf_CoreReduction
set_option autoImplicit false
namespace NBG_Reducer
open Aeneas Aeneas.Std Result AspisR1

theorem m31_reduce (x : U64) : ∃ z,
    FIo_Native.aspis_core.field.M31.reduce_u64 x = ok z ∧
      z.val = x.val % 2147483647 ∧ z.val < 2147483647 := by
  obtain ⟨z,run,value,bound⟩ := LPf_CoreReduction.source x
  exact ⟨z,by simp only [FIo_Native.aspis_core.field.M31.reduce_u64,run,bind_tc_ok],
    value,bound⟩

#print axioms m31_reduce
#print axioms AspisR1.LPf_CoreReduction.source
end NBG_Reducer
