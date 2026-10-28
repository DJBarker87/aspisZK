import R1Z.PV_Op223_Extract_08_M31_reduce_u64
import R1Z.PV_Op223_Agreement_M31_mul
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem M31_reduce_u64 : PV_Op223_Applied.aspis_core.field.M31.reduce_u64 = PV_Ext_IndexClosed.aspis_core.field.M31.reduce_u64 := by
  unfold PV_Op223_Applied.aspis_core.field.M31.reduce_u64 PV_Ext_IndexClosed.aspis_core.field.M31.reduce_u64
  simp only [R1Z.PV_Op223_Agreement.P, R1Z.PV_Op223_Agreement.ct_subtract_p, R1Z.PV_Op223_Agreement.ct_reduce64, R1Z.PV_Op223_Agreement.ct_add, R1Z.PV_Op223_Agreement.ct_sub, R1Z.PV_Op223_Agreement.M31_ZERO, R1Z.PV_Op223_Agreement.reduce_u64, R1Z.PV_Op223_Agreement.M31_mul]
#print axioms M31_reduce_u64
end R1Z.PV_Op223_Agreement
