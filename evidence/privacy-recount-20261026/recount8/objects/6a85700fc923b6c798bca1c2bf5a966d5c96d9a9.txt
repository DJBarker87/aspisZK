import R1Z.PV_Op223_Extract_02_ct_reduce64
import R1Z.PV_Op223_Agreement_ct_subtract_p
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem ct_reduce64 : PV_Op223_Applied.aspis_core.field.ct.reduce64 = PV_Ext_IndexClosed.aspis_core.field.ct.reduce64 := by
  unfold PV_Op223_Applied.aspis_core.field.ct.reduce64 PV_Ext_IndexClosed.aspis_core.field.ct.reduce64
  simp only [R1Z.PV_Op223_Agreement.P, R1Z.PV_Op223_Agreement.ct_subtract_p]
#print axioms ct_reduce64
end R1Z.PV_Op223_Agreement
