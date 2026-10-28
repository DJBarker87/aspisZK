import PV_B3P_NativeGroups226
import PV_B3P_ReadTwenty226
namespace PV_B3P_NativeIdentities226
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false

theorem fields_empty (out : alloc.vec.Vec U8) :
    PV_B3P_NativeFieldsVec226.fieldsVec out [] = .ok (.Ok out) := rfl

theorem frontier_groups (out : alloc.vec.Vec U8) (a : Array (Array U32 8#usize) 20#usize) :
    PV_B3P_NativeGroups226.groups out ((PV_B3P_ReadTwenty226.values a).map (fun row => row.val)) =
      PV_B3P_NativeFieldsVec226.fieldsVec out (PV_B3P_ByteLayout226V3.frontier a) := by
  rw [PV_B3P_ReadTwenty226.same,PV_B3P_NativeGroups226.complete_result]
  rfl

#print axioms fields_empty
#print axioms frontier_groups
end PV_B3P_NativeIdentities226
