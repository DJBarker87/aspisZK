import R1Z.PV_Ext_Closed_15_CM31_sub
import R1Z.PV_Ext_FieldBridge_M31_sub
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Ext_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem CM31_sub : PV_Ext_IndexClosed.aspis_core.field.CM31.sub = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub := by
  repeat' (apply funext; intro x)
  unfold PV_Ext_IndexClosed.aspis_core.field.CM31.sub R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub
  first | rfl | simpa only [R1Z.PV_Ext_FieldBridge.P, R1Z.PV_Ext_FieldBridge.ct_subtract_p, R1Z.PV_Ext_FieldBridge.ct_reduce64, R1Z.PV_Ext_FieldBridge.ct_add, R1Z.PV_Ext_FieldBridge.ct_sub, R1Z.PV_Ext_FieldBridge.M31_ZERO, R1Z.PV_Ext_FieldBridge.reduce_u64, R1Z.PV_Ext_FieldBridge.M31_mul, R1Z.PV_Ext_FieldBridge.M31_reduce_u64, R1Z.PV_Ext_FieldBridge.M31_add, R1Z.PV_Ext_FieldBridge.M31_double, R1Z.PV_Ext_FieldBridge.CM31_ZERO, R1Z.PV_Ext_FieldBridge.CM31_from_m31, R1Z.PV_Ext_FieldBridge.CM31_add, R1Z.PV_Ext_FieldBridge.M31_sub]
#print axioms CM31_sub
end R1Z.PV_Ext_FieldBridge
