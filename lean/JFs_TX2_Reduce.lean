import FIo_ReduceValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_Reduce
open Aeneas Aeneas.Std Result

theorem source (x : U64) : ∃ z,
    FIo_Native.aspis_core.field.M31.reduce_u64 x=ok z ∧ z.val<2147483647 := by
  obtain ⟨z,run,_,canon⟩ := ExtractedCurrentReducer.current_reduce_mod x
  refine ⟨z,?_,canon⟩
  unfold FIo_Native.aspis_core.field.M31.reduce_u64
  rw [FIo_ReduceBridge.same,FIo_ReduceValues.checked_probe,run]
  rfl

#print axioms source
end AspisR1.JFs_TX2_Reduce
end
