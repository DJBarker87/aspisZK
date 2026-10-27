import R1Z.PV_Ext_Closed_02_ct_reduce64
import R1Z.PV_Ext_FieldBridge_ct_subtract_p
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Ext_FieldBridge
/-- Exact complete-Result comparison of the freshly extracted candidate leaf
    field dependency with the retained current source, on arbitrary raw limbs. -/
theorem ct_reduce64 : PV_Ext_IndexClosed.aspis_core.field.ct.reduce64 = R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.reduce64 := by
  repeat' (apply funext; intro x)
  unfold PV_Ext_IndexClosed.aspis_core.field.ct.reduce64 R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.ct.reduce64
  first | rfl | simpa only [R1Z.PV_Ext_FieldBridge.P, R1Z.PV_Ext_FieldBridge.ct_subtract_p]
#print axioms ct_reduce64
end R1Z.PV_Ext_FieldBridge
