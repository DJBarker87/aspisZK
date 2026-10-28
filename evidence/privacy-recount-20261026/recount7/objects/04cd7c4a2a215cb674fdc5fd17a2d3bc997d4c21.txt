import R1Z.PV_B2_W_14_mul_by_r
import R1Z.PV_B2_Total_CM31_mul
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.mul_by_r
  (x : aspis_core.field.CM31) : aspis_core.field.CM31 :=
  let m := aspis_core.field.M31.double x.a
  let m1 := aspis_core.field.M31.sub m x.b
  let m2 := aspis_core.field.M31.double x.b
  let m3 := aspis_core.field.M31.add x.a m2
  { a := m1, b := m3 }
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem mul_by_r (x : ProverRwFull.aspis_core.field.CM31) : PV_B2_WeightsNative.aspis_core.field.mul_by_r x = ok (PV_B2_FieldValue.aspis_core.field.mul_by_r x) := by
  unfold PV_B2_WeightsNative.aspis_core.field.mul_by_r PV_B2_FieldValue.aspis_core.field.mul_by_r
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul, PV_B2_FieldTotal.M31_reduce_u64, PV_B2_FieldTotal.M31_add, PV_B2_FieldTotal.M31_double, PV_B2_FieldTotal.CM31_add, PV_B2_FieldTotal.M31_sub, PV_B2_FieldTotal.CM31_sub, PV_B2_FieldTotal.CM31_mul,lift,bind_tc_ok]
#print axioms mul_by_r
end PV_B2_FieldTotal
