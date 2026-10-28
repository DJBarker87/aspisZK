import R1Z.PV_Op223_Extract_04_ct_sub
import R1Z.PV_Op223_Agreement_ct_add
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem ct_sub : PV_Op223_Applied.aspis_core.field.ct.sub = PV_Ext_IndexClosed.aspis_core.field.ct.sub := by
  unfold PV_Op223_Applied.aspis_core.field.ct.sub PV_Ext_IndexClosed.aspis_core.field.ct.sub
  simp only [R1Z.PV_Op223_Agreement.P, R1Z.PV_Op223_Agreement.ct_subtract_p, R1Z.PV_Op223_Agreement.ct_reduce64, R1Z.PV_Op223_Agreement.ct_add]
#print axioms ct_sub
end R1Z.PV_Op223_Agreement
