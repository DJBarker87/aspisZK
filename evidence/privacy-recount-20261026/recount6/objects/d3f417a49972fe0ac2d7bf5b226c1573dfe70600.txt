import R1Z.PV_Ext_Closed_01_ct_subtract_p
import R1Z.PV_Ext_FieldBridge_P
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Ext_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem ct_subtract_p : PV_Ext_IndexClosed.aspis_core.field.ct.subtract_p = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.subtract_p := by
  funext x
  unfold PV_Ext_IndexClosed.aspis_core.field.ct.subtract_p ProverRwP7CurrentFieldSource.aspis_core.field.ct.subtract_p
  rw [P]
#print axioms ct_subtract_p
end R1Z.PV_Ext_FieldBridge
