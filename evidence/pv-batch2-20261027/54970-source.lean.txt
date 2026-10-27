import R1Z.PV_B2_W_01_ct_subtract_p
import R1Z.PV_B2_Total_P
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.ct.subtract_p (x : Std.U32) : Std.U32 :=
  let i := (UScalar.cast_fromBool .U32 (x >= aspis_core.field.P))
  let mask := (core.num.U32.wrapping_sub 0#u32 i)
  let i1 := (aspis_core.field.P &&& mask)
  (core.num.U32.wrapping_sub x i1)
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem ct_subtract_p (x : Std.U32) : PV_B2_WeightsNative.aspis_core.field.ct.subtract_p x = ok (PV_B2_FieldValue.aspis_core.field.ct.subtract_p x) := by
  unfold PV_B2_WeightsNative.aspis_core.field.ct.subtract_p PV_B2_FieldValue.aspis_core.field.ct.subtract_p
  simp only [PV_B2_FieldTotal.P,lift,bind_tc_ok]
#print axioms ct_subtract_p
end PV_B2_FieldTotal
