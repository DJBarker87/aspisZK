import R1Z.PV_B2_W_07_M31_reduce_u64
import R1Z.PV_B2_Total_M31_mul
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.M31.reduce_u64
  (value : Std.U64) : aspis_core.field.M31 :=
  let i := aspis_core.field.reduce_u64 value
  i
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem M31_reduce_u64 (value : Std.U64) : PV_B2_WeightsNative.aspis_core.field.M31.reduce_u64 value = ok (PV_B2_FieldValue.aspis_core.field.M31.reduce_u64 value) := by
  unfold PV_B2_WeightsNative.aspis_core.field.M31.reduce_u64 PV_B2_FieldValue.aspis_core.field.M31.reduce_u64
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul,lift,bind_tc_ok]
#print axioms M31_reduce_u64
end PV_B2_FieldTotal
