import R1Z.PV_Ext_Closed_22_QM31_mul_m31
import R1Z.PV_Op223_FieldBridge_QM31_mul
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem QM31_mul_m31 : PV_Ext_IndexClosed.aspis_core.field.QM31.mul_m31 = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31 := by
  funext a b
  unfold PV_Ext_IndexClosed.aspis_core.field.QM31.mul_m31 R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31
  simp only [R1Z.PV_Op223_FieldBridge.CM31_mul_m31]
#print axioms QM31_mul_m31
end R1Z.PV_Op223_FieldBridge
