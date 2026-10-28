import R1Z.PV_Ext_Closed_03_ct_add
import R1Z.PV_Ext_FieldBridge_ct_reduce64
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Ext_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem ct_add : PV_Ext_IndexClosed.aspis_core.field.ct.add = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.add := by
  repeat' (apply funext; intro x)
  unfold PV_Ext_IndexClosed.aspis_core.field.ct.add R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.add
  first | rfl | simpa only [R1Z.PV_Ext_FieldBridge.P, R1Z.PV_Ext_FieldBridge.ct_subtract_p, R1Z.PV_Ext_FieldBridge.ct_reduce64]
#print axioms ct_add
end R1Z.PV_Ext_FieldBridge
