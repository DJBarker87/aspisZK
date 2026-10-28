import R1Z.PV_Ext_Closed_10_M31_double
import R1Z.PV_Ext_FieldBridge_M31_add
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Ext_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem M31_double : PV_Ext_IndexClosed.aspis_core.field.M31.double = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.double := by
  repeat' (apply funext; intro x)
  unfold PV_Ext_IndexClosed.aspis_core.field.M31.double R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.double
  first | rfl | simpa only [R1Z.PV_Ext_FieldBridge.P, R1Z.PV_Ext_FieldBridge.ct_subtract_p, R1Z.PV_Ext_FieldBridge.ct_reduce64, R1Z.PV_Ext_FieldBridge.ct_add, R1Z.PV_Ext_FieldBridge.ct_sub, R1Z.PV_Ext_FieldBridge.M31_ZERO, R1Z.PV_Ext_FieldBridge.reduce_u64, R1Z.PV_Ext_FieldBridge.M31_mul, R1Z.PV_Ext_FieldBridge.M31_reduce_u64, R1Z.PV_Ext_FieldBridge.M31_add]
#print axioms M31_double
end R1Z.PV_Ext_FieldBridge
