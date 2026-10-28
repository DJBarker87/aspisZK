import R1Z.PV_Op223_Extract_09_M31_add
import R1Z.PV_Op223_Agreement_M31_reduce_u64
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem M31_add : PV_Op223_Applied.aspis_core.field.M31.add = PV_Ext_IndexClosed.aspis_core.field.M31.add := by
  unfold PV_Op223_Applied.aspis_core.field.M31.add PV_Ext_IndexClosed.aspis_core.field.M31.add
  simp only [R1Z.PV_Op223_Agreement.P, R1Z.PV_Op223_Agreement.ct_subtract_p, R1Z.PV_Op223_Agreement.ct_reduce64, R1Z.PV_Op223_Agreement.ct_add, R1Z.PV_Op223_Agreement.ct_sub, R1Z.PV_Op223_Agreement.M31_ZERO, R1Z.PV_Op223_Agreement.reduce_u64, R1Z.PV_Op223_Agreement.M31_mul, R1Z.PV_Op223_Agreement.M31_reduce_u64]
#print axioms M31_add
end R1Z.PV_Op223_Agreement
