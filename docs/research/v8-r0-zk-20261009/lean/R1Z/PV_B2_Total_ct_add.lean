import R1Z.PV_B2_W_03_ct_add
import R1Z.PV_B2_Total_ct_reduce64
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.ct.add (a : Std.U32) (b : Std.U32) : Std.U32 :=
  let i := (core.num.U32.wrapping_add a b)
  aspis_core.field.ct.subtract_p i
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem ct_add (a : Std.U32) (b : Std.U32) : PV_B2_WeightsNative.aspis_core.field.ct.add a b = ok (PV_B2_FieldValue.aspis_core.field.ct.add a b) := by
  unfold PV_B2_WeightsNative.aspis_core.field.ct.add PV_B2_FieldValue.aspis_core.field.ct.add
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64,lift,bind_tc_ok]
#print axioms ct_add
end PV_B2_FieldTotal
