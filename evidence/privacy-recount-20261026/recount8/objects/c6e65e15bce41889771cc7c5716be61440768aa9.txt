import R1Z.PV_Op223_Extract_05_M31_ZERO
import R1Z.PV_Op223_Agreement_ct_sub
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem M31_ZERO : PV_Op223_Applied.aspis_core.field.M31.ZERO = PV_Ext_IndexClosed.aspis_core.field.M31.ZERO := by
  unfold PV_Op223_Applied.aspis_core.field.M31.ZERO PV_Ext_IndexClosed.aspis_core.field.M31.ZERO
  simp only [R1Z.PV_Op223_Agreement.P, R1Z.PV_Op223_Agreement.ct_subtract_p, R1Z.PV_Op223_Agreement.ct_reduce64, R1Z.PV_Op223_Agreement.ct_add, R1Z.PV_Op223_Agreement.ct_sub]
#print axioms M31_ZERO
end R1Z.PV_Op223_Agreement
