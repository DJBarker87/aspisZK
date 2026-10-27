import R1Z.PV_B2_W_18_QM31_sub
import R1Z.PV_B2_Total_QM31_add
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.QM31.sub
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  aspis_core.field.QM31
  :=
  let c := aspis_core.field.CM31.sub self.c0 rhs.c0
  let c1 := aspis_core.field.CM31.sub self.c1 rhs.c1
  { c0 := c, c1 }
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem QM31_sub (self : ProverRwFull.aspis_core.field.QM31) (rhs : ProverRwFull.aspis_core.field.QM31) : PV_B2_WeightsNative.aspis_core.field.QM31.sub self rhs = ok (PV_B2_FieldValue.aspis_core.field.QM31.sub self rhs) := by
  unfold PV_B2_WeightsNative.aspis_core.field.QM31.sub PV_B2_FieldValue.aspis_core.field.QM31.sub
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul, PV_B2_FieldTotal.M31_reduce_u64, PV_B2_FieldTotal.M31_add, PV_B2_FieldTotal.M31_double, PV_B2_FieldTotal.CM31_add, PV_B2_FieldTotal.M31_sub, PV_B2_FieldTotal.CM31_sub, PV_B2_FieldTotal.CM31_mul, PV_B2_FieldTotal.mul_by_r, PV_B2_FieldTotal.QM31_ZERO, PV_B2_FieldTotal.QM31_ONE, PV_B2_FieldTotal.QM31_add,lift,bind_tc_ok]
#print axioms QM31_sub
end PV_B2_FieldTotal
