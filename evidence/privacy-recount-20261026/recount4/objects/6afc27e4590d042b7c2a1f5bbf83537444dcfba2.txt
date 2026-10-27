import R1Z.PV_Op223_Extract_10_M31_double
import R1Z.PV_Op223_Agreement_M31_add
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem M31_double : PV_Op223_Applied.aspis_core.field.M31.double = PV_Ext_IndexClosed.aspis_core.field.M31.double := by
  unfold PV_Op223_Applied.aspis_core.field.M31.double PV_Ext_IndexClosed.aspis_core.field.M31.double
  simp only [R1Z.PV_Op223_Agreement.P, R1Z.PV_Op223_Agreement.ct_subtract_p, R1Z.PV_Op223_Agreement.ct_reduce64, R1Z.PV_Op223_Agreement.ct_add, R1Z.PV_Op223_Agreement.ct_sub, R1Z.PV_Op223_Agreement.M31_ZERO, R1Z.PV_Op223_Agreement.reduce_u64, R1Z.PV_Op223_Agreement.M31_mul, R1Z.PV_Op223_Agreement.M31_reduce_u64, R1Z.PV_Op223_Agreement.M31_add]
#print axioms M31_double
end R1Z.PV_Op223_Agreement
