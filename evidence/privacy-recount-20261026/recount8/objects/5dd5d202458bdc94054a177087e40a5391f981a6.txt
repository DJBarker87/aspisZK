import R1Z.PV_Ext_Closed_21_QM31_mul
import R1Z.PV_Op223_FieldBridge_QM31_add
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem QM31_mul : PV_Ext_IndexClosed.aspis_core.field.QM31.mul = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul := by
  funext a b
  unfold PV_Ext_IndexClosed.aspis_core.field.QM31.mul R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul
  simp only [R1Z.PV_Ext_FieldBridge.CM31_mul, R1Z.PV_Ext_FieldBridge.CM31_add, R1Z.PV_Ext_FieldBridge.CM31_sub, R1Z.PV_Op223_FieldBridge.mul_by_r]
#print axioms QM31_mul
end R1Z.PV_Op223_FieldBridge
