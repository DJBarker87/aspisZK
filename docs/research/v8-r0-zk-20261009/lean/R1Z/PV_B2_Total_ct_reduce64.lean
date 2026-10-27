import R1Z.PV_B2_W_02_ct_reduce64
import R1Z.PV_B2_Total_ct_subtract_p
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.ct.reduce64 (x : Std.U64) : Std.U32 :=
  let i := (UScalar.cast .U64 aspis_core.field.P)
  let i1 := (x &&& i)
  let i2 := (Std.U64.wrapping_shr x 31#u32)
  let x1 := (Std.U64.wrapping_add i1 i2)
  let i3 := (UScalar.cast .U64 aspis_core.field.P)
  let i4 := (x1 &&& i3)
  let i5 := (Std.U64.wrapping_shr x1 31#u32)
  let x2 := (Std.U64.wrapping_add i4 i5)
  let i6 := (UScalar.cast .U32 x2)
  aspis_core.field.ct.subtract_p i6
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem ct_reduce64 (x : Std.U64) : PV_B2_WeightsNative.aspis_core.field.ct.reduce64 x = ok (PV_B2_FieldValue.aspis_core.field.ct.reduce64 x) := by
  unfold PV_B2_WeightsNative.aspis_core.field.ct.reduce64 PV_B2_FieldValue.aspis_core.field.ct.reduce64
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p,lift,bind_tc_ok]
#print axioms ct_reduce64
end PV_B2_FieldTotal
