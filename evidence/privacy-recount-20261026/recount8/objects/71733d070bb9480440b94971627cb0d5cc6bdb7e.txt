import R1Z.PV_Op223_Extract_06_reduce_u64
import R1Z.PV_Op223_Agreement_M31_ZERO
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem reduce_u64 : PV_Op223_Applied.aspis_core.field.reduce_u64 = PV_Ext_IndexClosed.aspis_core.field.reduce_u64 := by
  unfold PV_Op223_Applied.aspis_core.field.reduce_u64 PV_Ext_IndexClosed.aspis_core.field.reduce_u64
  simp only [R1Z.PV_Op223_Agreement.P, R1Z.PV_Op223_Agreement.ct_subtract_p, R1Z.PV_Op223_Agreement.ct_reduce64, R1Z.PV_Op223_Agreement.ct_add, R1Z.PV_Op223_Agreement.ct_sub, R1Z.PV_Op223_Agreement.M31_ZERO]
#print axioms reduce_u64
end R1Z.PV_Op223_Agreement
