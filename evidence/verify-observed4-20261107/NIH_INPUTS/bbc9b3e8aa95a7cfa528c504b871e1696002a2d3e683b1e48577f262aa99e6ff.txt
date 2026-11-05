import NHU_COMBINED_IMPORT
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_SelectedBinary
open FIq_Native.pool_v1.pair_forest_copy_terminal
/-- Complete emitted helper, including all nonbinary raw weights. -/
theorem result (high : FIq_Native.field.QM31) (weight : U32) :
 selected_binary_weight high weight=ok
 (if weight=1#u32 then high else NHU_Lift.reference 0#u32) := by
 simp only [selected_binary_weight,FIq_Native.field.QM31.ZERO,
  FIq_Native.field.CM31.ZERO,FIq_Native.field.M31.ZERO,NHU_Lift.reference,lift,bind_tc_ok]
 rfl
#print axioms result
end AspisR1.NIH_SelectedBinary
