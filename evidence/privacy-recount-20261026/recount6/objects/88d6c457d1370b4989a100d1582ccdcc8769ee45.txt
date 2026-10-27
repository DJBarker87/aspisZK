import R1Z.PV_Op223_Extract_01_ct_subtract_p
import R1Z.PV_Op223_Agreement_P
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem ct_subtract_p : PV_Op223_Applied.aspis_core.field.ct.subtract_p = PV_Ext_IndexClosed.aspis_core.field.ct.subtract_p := by
  unfold PV_Op223_Applied.aspis_core.field.ct.subtract_p PV_Ext_IndexClosed.aspis_core.field.ct.subtract_p
  simp only [R1Z.PV_Op223_Agreement.P]
#print axioms ct_subtract_p
end R1Z.PV_Op223_Agreement
