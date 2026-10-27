import R1Z.PV_B2_W_06_M31_mul
import R1Z.PV_B2_Total_reduce_u64
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.M31.mul
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  aspis_core.field.M31
  :=
  let i := (UScalar.cast .U64 self)
  let i1 := (UScalar.cast .U64 rhs)
  let i2 := (Std.U64.wrapping_mul i i1)
  let i3 := aspis_core.field.reduce_u64 i2
  i3
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem M31_mul (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) : PV_B2_WeightsNative.aspis_core.field.M31.mul self rhs = ok (PV_B2_FieldValue.aspis_core.field.M31.mul self rhs) := by
  unfold PV_B2_WeightsNative.aspis_core.field.M31.mul PV_B2_FieldValue.aspis_core.field.M31.mul
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64,lift,bind_tc_ok]
#print axioms M31_mul
end PV_B2_FieldTotal
