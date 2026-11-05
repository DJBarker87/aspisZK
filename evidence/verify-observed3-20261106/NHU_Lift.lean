import NHG_COMBINED_IMPORT
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_Lift
/-- Safe reference constructor uses the same two fixed CM31 records and no
field arithmetic. This domain includes every raw u32. -/
def reference (value : U32) : FIq_Native.field.QM31 :=
 ⟨⟨value,0#u32⟩,⟨0#u32,0#u32⟩⟩
theorem result (value : U32) :
 FIq_Native.pool_v1.pair_forest_semantic_terminal.lift_m31 value=ok (reference value) := by
 simp only [FIq_Native.pool_v1.pair_forest_semantic_terminal.lift_m31,
  FIq_Native.field.CM31.from_m31,FIq_Native.field.QM31.from_cm31,
  FIq_Native.field.M31.ZERO,FIq_Native.field.CM31.ZERO,bind_tc_ok]
 rfl
#print axioms result
end AspisR1.NHU_Lift
