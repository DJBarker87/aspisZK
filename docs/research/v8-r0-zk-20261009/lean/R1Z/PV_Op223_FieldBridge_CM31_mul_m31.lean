import R1Z.PV_Ext_Closed_17_CM31_mul_m31
import R1Z.PV_Ext_FieldBridge_CM31_mul
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem CM31_mul_m31 : PV_Ext_IndexClosed.aspis_core.field.CM31.mul_m31 = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul_m31 := by
  funext a b
  unfold PV_Ext_IndexClosed.aspis_core.field.CM31.mul_m31 R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul_m31
  simp only [R1Z.PV_Ext_FieldBridge.M31_mul]
#print axioms CM31_mul_m31
end R1Z.PV_Op223_FieldBridge
