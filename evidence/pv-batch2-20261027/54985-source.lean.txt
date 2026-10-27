import R1Z.PV_B2_W_15_QM31_ZERO
import R1Z.PV_B2_Total_mul_by_r
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.QM31.ZERO : aspis_core.field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem QM31_ZERO : PV_B2_WeightsNative.aspis_core.field.QM31.ZERO = PV_B2_FieldValue.aspis_core.field.QM31.ZERO := by
  unfold PV_B2_WeightsNative.aspis_core.field.QM31.ZERO PV_B2_FieldValue.aspis_core.field.QM31.ZERO
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul, PV_B2_FieldTotal.M31_reduce_u64, PV_B2_FieldTotal.M31_add, PV_B2_FieldTotal.M31_double, PV_B2_FieldTotal.CM31_add, PV_B2_FieldTotal.M31_sub, PV_B2_FieldTotal.CM31_sub, PV_B2_FieldTotal.CM31_mul, PV_B2_FieldTotal.mul_by_r,lift,bind_tc_ok]
#print axioms QM31_ZERO
end PV_B2_FieldTotal
