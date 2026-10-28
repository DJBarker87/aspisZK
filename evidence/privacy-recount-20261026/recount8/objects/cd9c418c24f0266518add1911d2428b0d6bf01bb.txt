import R1Z.PV_Ext_Closed_00_P
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Ext_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem P : PV_Ext_IndexClosed.aspis_core.field.P = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.P := by
  simp only [PV_Ext_IndexClosed.aspis_core.field.P, R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.P]
#print axioms P
end R1Z.PV_Ext_FieldBridge
