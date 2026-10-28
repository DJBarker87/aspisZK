import R1Z.PV_Op223_Extract_20_QM31_add
import R1Z.PV_Op223_Agreement_QM31_from_cm31
open Aeneas Aeneas.Std Result
namespace R1Z.PV_Op223_Agreement
theorem QM31_add : PV_Op223_Applied.aspis_core.field.QM31.add = PV_Ext_IndexClosed.aspis_core.field.QM31.add := by
  unfold PV_Op223_Applied.aspis_core.field.QM31.add PV_Ext_IndexClosed.aspis_core.field.QM31.add
  simp only [R1Z.PV_Op223_Agreement.P, R1Z.PV_Op223_Agreement.ct_subtract_p, R1Z.PV_Op223_Agreement.ct_reduce64, R1Z.PV_Op223_Agreement.ct_add, R1Z.PV_Op223_Agreement.ct_sub, R1Z.PV_Op223_Agreement.M31_ZERO, R1Z.PV_Op223_Agreement.reduce_u64, R1Z.PV_Op223_Agreement.M31_mul, R1Z.PV_Op223_Agreement.M31_reduce_u64, R1Z.PV_Op223_Agreement.M31_add, R1Z.PV_Op223_Agreement.M31_double, R1Z.PV_Op223_Agreement.CM31_ZERO, R1Z.PV_Op223_Agreement.CM31_from_m31, R1Z.PV_Op223_Agreement.CM31_add, R1Z.PV_Op223_Agreement.M31_sub, R1Z.PV_Op223_Agreement.CM31_sub, R1Z.PV_Op223_Agreement.CM31_mul, R1Z.PV_Op223_Agreement.CM31_mul_m31, R1Z.PV_Op223_Agreement.mul_by_r, R1Z.PV_Op223_Agreement.QM31_from_cm31]
#print axioms QM31_add
end R1Z.PV_Op223_Agreement
