import R1Z.PV_Ext_Closed_18_mul_by_r
import R1Z.PV_Op223_FieldBridge_CM31_mul_m31
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem mul_by_r : PV_Ext_IndexClosed.aspis_core.field.mul_by_r = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r := by
  funext a
  unfold PV_Ext_IndexClosed.aspis_core.field.mul_by_r R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r
  simp only [R1Z.PV_Ext_FieldBridge.M31_double, R1Z.PV_Ext_FieldBridge.M31_add, R1Z.PV_Ext_FieldBridge.M31_sub]
#print axioms mul_by_r
end R1Z.PV_Op223_FieldBridge
