import R1Z.PV_B2_W_19_QM31_mul
import R1Z.PV_B2_Total_QM31_sub
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.QM31.mul
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  aspis_core.field.QM31
  :=
  let m0 := aspis_core.field.CM31.mul self.c0 rhs.c0
  let m1 := aspis_core.field.CM31.mul self.c1 rhs.c1
  let c := aspis_core.field.CM31.add self.c0 self.c1
  let c1 := aspis_core.field.CM31.add rhs.c0 rhs.c1
  let m2 := aspis_core.field.CM31.mul c c1
  let c2 := aspis_core.field.mul_by_r m1
  let c3 := aspis_core.field.CM31.add m0 c2
  let c4 := aspis_core.field.CM31.sub m2 m0
  let c5 := aspis_core.field.CM31.sub c4 m1
  { c0 := c3, c1 := c5 }
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem QM31_mul (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) : PV_B2_WeightsNative.aspis_core.field.QM31.mul self rhs = ok (PV_B2_FieldValue.aspis_core.field.QM31.mul self rhs) := by
  unfold PV_B2_WeightsNative.aspis_core.field.QM31.mul PV_B2_FieldValue.aspis_core.field.QM31.mul
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul, PV_B2_FieldTotal.M31_reduce_u64, PV_B2_FieldTotal.M31_add, PV_B2_FieldTotal.M31_double, PV_B2_FieldTotal.CM31_add, PV_B2_FieldTotal.M31_sub, PV_B2_FieldTotal.CM31_sub, PV_B2_FieldTotal.CM31_mul, PV_B2_FieldTotal.mul_by_r, PV_B2_FieldTotal.QM31_ZERO, PV_B2_FieldTotal.QM31_ONE, PV_B2_FieldTotal.QM31_add, PV_B2_FieldTotal.QM31_sub,lift,bind_tc_ok]
#print axioms QM31_mul
end PV_B2_FieldTotal
