import FIo_FieldBridge
import FIo_ReduceBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_ReduceBridge
open Aeneas Aeneas.Std Result

theorem same (x : U64) :
    FIo_Native.aspis_core.field.reduce_u64 x=AspisR1CurrentWide.field.reduce_u64 x := by
  simp only [FIo_Native.aspis_core.field.reduce_u64,AspisR1CurrentWide.field.reduce_u64,
    FIo_Native.aspis_core.field.P,AspisR1CurrentWide.field.P,lift,bind_tc_ok,FIo_ReduceFacts.shr31]
  rw [FIo_ReduceBounds.checked x]
  simp only [bind_tc_ok,FIo_ReduceFacts.shr31]
  rw [FIo_ReduceBounds.checked (FIo_ReduceBounds.fold x)]
  simp only [bind_tc_ok]
  split
  · rename_i h
    rw [FIo_ScalarBridge.sub _ (2147483647#u32) (by scalar_tac)]
  · rfl

#print axioms same
end AspisR1.FIo_ReduceBridge
end
