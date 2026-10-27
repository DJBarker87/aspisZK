import R1Z.PV_Ext_Closed_08_M31_reduce_u64
import R1Z.PV_Ext_FieldBridge_M31_mul
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Ext_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem M31_reduce_u64 : PV_Ext_IndexClosed.aspis_core.field.M31.reduce_u64 = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.reduce_u64 := by
  repeat' (apply funext; intro x)
  unfold PV_Ext_IndexClosed.aspis_core.field.M31.reduce_u64 R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.reduce_u64
  first | rfl | simpa only [R1Z.PV_Ext_FieldBridge.P, R1Z.PV_Ext_FieldBridge.ct_subtract_p, R1Z.PV_Ext_FieldBridge.ct_reduce64, R1Z.PV_Ext_FieldBridge.ct_add, R1Z.PV_Ext_FieldBridge.ct_sub, R1Z.PV_Ext_FieldBridge.M31_ZERO, R1Z.PV_Ext_FieldBridge.reduce_u64, R1Z.PV_Ext_FieldBridge.M31_mul]
#print axioms M31_reduce_u64
end R1Z.PV_Ext_FieldBridge
