import R1Z.PV_Ext_Closed_21_QM31_mul
import R1Z.PV_Op223_FieldBridge_QM31_add
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem QM31_mul : PV_Ext_IndexClosed.aspis_core.field.QM31.mul = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul := by
  repeat' (apply funext; intro x)
  unfold PV_Ext_IndexClosed.aspis_core.field.QM31.mul R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul
  first | rfl | simpa only [R1Z.PV_Ext_FieldBridge.P, R1Z.PV_Ext_FieldBridge.ct_subtract_p, R1Z.PV_Ext_FieldBridge.ct_reduce64, R1Z.PV_Ext_FieldBridge.ct_add, R1Z.PV_Ext_FieldBridge.ct_sub, R1Z.PV_Ext_FieldBridge.M31_ZERO, R1Z.PV_Ext_FieldBridge.reduce_u64, R1Z.PV_Ext_FieldBridge.M31_mul, R1Z.PV_Ext_FieldBridge.M31_reduce_u64, R1Z.PV_Ext_FieldBridge.M31_add, R1Z.PV_Ext_FieldBridge.M31_double, R1Z.PV_Ext_FieldBridge.CM31_ZERO, R1Z.PV_Ext_FieldBridge.CM31_from_m31, R1Z.PV_Ext_FieldBridge.CM31_add, R1Z.PV_Ext_FieldBridge.M31_sub, R1Z.PV_Ext_FieldBridge.CM31_sub, R1Z.PV_Ext_FieldBridge.CM31_mul, R1Z.PV_Op223_FieldBridge.CM31_mul_m31, R1Z.PV_Op223_FieldBridge.mul_by_r, R1Z.PV_Op223_FieldBridge.QM31_from_cm31, R1Z.PV_Op223_FieldBridge.QM31_add]
#print axioms QM31_mul
end R1Z.PV_Op223_FieldBridge
