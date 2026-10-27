import R1Z.PV_Ext_Closed_13_CM31_add
import R1Z.PV_Ext_FieldBridge_CM31_from_m31
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Ext_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem CM31_add : PV_Ext_IndexClosed.aspis_core.field.CM31.add = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.add := by
  repeat' (apply funext; intro x)
  unfold PV_Ext_IndexClosed.aspis_core.field.CM31.add R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.add
  first | rfl | simpa only [R1Z.PV_Ext_FieldBridge.P, R1Z.PV_Ext_FieldBridge.ct_subtract_p, R1Z.PV_Ext_FieldBridge.ct_reduce64, R1Z.PV_Ext_FieldBridge.ct_add, R1Z.PV_Ext_FieldBridge.ct_sub, R1Z.PV_Ext_FieldBridge.M31_ZERO, R1Z.PV_Ext_FieldBridge.reduce_u64, R1Z.PV_Ext_FieldBridge.M31_mul, R1Z.PV_Ext_FieldBridge.M31_reduce_u64, R1Z.PV_Ext_FieldBridge.M31_add, R1Z.PV_Ext_FieldBridge.M31_double, R1Z.PV_Ext_FieldBridge.CM31_ZERO, R1Z.PV_Ext_FieldBridge.CM31_from_m31]
#print axioms CM31_add
end R1Z.PV_Ext_FieldBridge
