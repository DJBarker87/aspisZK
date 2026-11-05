import NHU_Lift
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_CopyLift
/-- Actual emitted copy-terminal helper, all raw u32 including noncanonical. -/
theorem result (value : U32) :
 FIq_Native.pool_v1.pair_forest_copy_terminal.lift_m31 value=
 ok (NHU_Lift.reference value) := by
 simp only [FIq_Native.pool_v1.pair_forest_copy_terminal.lift_m31,
  FIq_Native.field.CM31.from_m31,FIq_Native.field.QM31.from_cm31,
  FIq_Native.field.M31.ZERO,FIq_Native.field.CM31.ZERO,bind_tc_ok]
 rfl
#print axioms result
end AspisR1.NIH_CopyLift
