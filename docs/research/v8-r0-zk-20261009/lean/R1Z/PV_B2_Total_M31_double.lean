import R1Z.PV_B2_W_09_M31_double
import R1Z.PV_B2_Total_M31_add
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.M31.double
  (self : aspis_core.field.M31) : aspis_core.field.M31 :=
  aspis_core.field.M31.add self self
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem M31_double (self : aspis_core.field.M31) : PV_B2_WeightsNative.aspis_core.field.M31.double self = ok (PV_B2_FieldValue.aspis_core.field.M31.double self) := by
  unfold PV_B2_WeightsNative.aspis_core.field.M31.double PV_B2_FieldValue.aspis_core.field.M31.double
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul, PV_B2_FieldTotal.M31_reduce_u64, PV_B2_FieldTotal.M31_add,lift,bind_tc_ok]
#print axioms M31_double
end PV_B2_FieldTotal
