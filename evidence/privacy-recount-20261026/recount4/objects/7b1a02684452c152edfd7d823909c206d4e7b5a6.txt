import R1Z.PV_Op223_Extract_11_CM31_ZERO
import R1Z.PV_Op223_Agreement_M31_double
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem CM31_ZERO : PV_Op223_Applied.aspis_core.field.CM31.ZERO = PV_Ext_IndexClosed.aspis_core.field.CM31.ZERO := by
  unfold PV_Op223_Applied.aspis_core.field.CM31.ZERO PV_Ext_IndexClosed.aspis_core.field.CM31.ZERO
  simp only [R1Z.PV_Op223_Agreement.P, R1Z.PV_Op223_Agreement.ct_subtract_p, R1Z.PV_Op223_Agreement.ct_reduce64, R1Z.PV_Op223_Agreement.ct_add, R1Z.PV_Op223_Agreement.ct_sub, R1Z.PV_Op223_Agreement.M31_ZERO, R1Z.PV_Op223_Agreement.reduce_u64, R1Z.PV_Op223_Agreement.M31_mul, R1Z.PV_Op223_Agreement.M31_reduce_u64, R1Z.PV_Op223_Agreement.M31_add, R1Z.PV_Op223_Agreement.M31_double]
#print axioms CM31_ZERO
end R1Z.PV_Op223_Agreement
