import R1Z.PV_Ext_Closed_04_ct_sub
import R1Z.PV_Ext_FieldBridge_ct_add
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Ext_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem ct_sub : PV_Ext_IndexClosed.aspis_core.field.ct.sub = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.sub := by
  repeat' (apply funext; intro x)
  unfold PV_Ext_IndexClosed.aspis_core.field.ct.sub R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.sub
  first | rfl | simpa only [R1Z.PV_Ext_FieldBridge.P, R1Z.PV_Ext_FieldBridge.ct_subtract_p, R1Z.PV_Ext_FieldBridge.ct_reduce64, R1Z.PV_Ext_FieldBridge.ct_add]
#print axioms ct_sub
end R1Z.PV_Ext_FieldBridge
