import R1Z.PV_Op223_Extract_03_ct_add
import R1Z.PV_Op223_Agreement_ct_reduce64
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem ct_add : PV_Op223_Applied.aspis_core.field.ct.add = PV_Ext_IndexClosed.aspis_core.field.ct.add := by
  unfold PV_Op223_Applied.aspis_core.field.ct.add PV_Ext_IndexClosed.aspis_core.field.ct.add
  simp only [R1Z.PV_Op223_Agreement.P, R1Z.PV_Op223_Agreement.ct_subtract_p, R1Z.PV_Op223_Agreement.ct_reduce64]
#print axioms ct_add
end R1Z.PV_Op223_Agreement
