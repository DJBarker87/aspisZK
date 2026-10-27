import R1Z.PV_B2_W_05_reduce_u64
import R1Z.PV_B2_Total_ct_sub
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.reduce_u64 (x : Std.U64) : Std.U32 :=
  aspis_core.field.ct.reduce64 x
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem reduce_u64 (x : Std.U64) : PV_B2_WeightsNative.aspis_core.field.reduce_u64 x = ok (PV_B2_FieldValue.aspis_core.field.reduce_u64 x) := by
  unfold PV_B2_WeightsNative.aspis_core.field.reduce_u64 PV_B2_FieldValue.aspis_core.field.reduce_u64
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub,lift,bind_tc_ok]
#print axioms reduce_u64
end PV_B2_FieldTotal
