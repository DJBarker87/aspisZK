import R1Z.PV_Op223_Extract_07_M31_mul
import R1Z.PV_Op223_Agreement_reduce_u64
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem M31_mul : PV_Op223_Applied.aspis_core.field.M31.mul = PV_Ext_IndexClosed.aspis_core.field.M31.mul := by
  unfold PV_Op223_Applied.aspis_core.field.M31.mul PV_Ext_IndexClosed.aspis_core.field.M31.mul
  simp only [R1Z.PV_Op223_Agreement.P, R1Z.PV_Op223_Agreement.ct_subtract_p, R1Z.PV_Op223_Agreement.ct_reduce64, R1Z.PV_Op223_Agreement.ct_add, R1Z.PV_Op223_Agreement.ct_sub, R1Z.PV_Op223_Agreement.M31_ZERO, R1Z.PV_Op223_Agreement.reduce_u64]
#print axioms M31_mul
end R1Z.PV_Op223_Agreement
