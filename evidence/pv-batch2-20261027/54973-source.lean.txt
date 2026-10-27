import R1Z.PV_B2_W_04_ct_sub
import R1Z.PV_B2_Total_ct_add
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.ct.sub (a : Std.U32) (b : Std.U32) : Std.U32 :=
  let i := (core.num.U32.wrapping_add a aspis_core.field.P)
  let i1 := (core.num.U32.wrapping_sub i b)
  aspis_core.field.ct.subtract_p i1
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem ct_sub (a : Std.U32) (b : Std.U32) : PV_B2_WeightsNative.aspis_core.field.ct.sub a b = ok (PV_B2_FieldValue.aspis_core.field.ct.sub a b) := by
  unfold PV_B2_WeightsNative.aspis_core.field.ct.sub PV_B2_FieldValue.aspis_core.field.ct.sub
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add,lift,bind_tc_ok]
#print axioms ct_sub
end PV_B2_FieldTotal
