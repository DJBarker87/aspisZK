import R1Z.PV_Ext_Closed_20_QM31_add
import R1Z.PV_Op223_FieldBridge_QM31_from_cm31
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem QM31_add : PV_Ext_IndexClosed.aspis_core.field.QM31.add = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add := by
  funext a b
  unfold PV_Ext_IndexClosed.aspis_core.field.QM31.add R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add
  simp only [R1Z.PV_Ext_FieldBridge.CM31_add]
#print axioms QM31_add
end R1Z.PV_Op223_FieldBridge
