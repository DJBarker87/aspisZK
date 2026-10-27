import R1Z.PV_B2_W_12_CM31_sub
import R1Z.PV_B2_Total_M31_sub
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.CM31.sub
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  aspis_core.field.CM31
  :=
  let m := aspis_core.field.M31.sub self.a rhs.a
  let m1 := aspis_core.field.M31.sub self.b rhs.b
  { a := m, b := m1 }
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem CM31_sub (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) : PV_B2_WeightsNative.aspis_core.field.CM31.sub self rhs = ok (PV_B2_FieldValue.aspis_core.field.CM31.sub self rhs) := by
  unfold PV_B2_WeightsNative.aspis_core.field.CM31.sub PV_B2_FieldValue.aspis_core.field.CM31.sub
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul, PV_B2_FieldTotal.M31_reduce_u64, PV_B2_FieldTotal.M31_add, PV_B2_FieldTotal.M31_double, PV_B2_FieldTotal.CM31_add, PV_B2_FieldTotal.M31_sub,lift,bind_tc_ok]
#print axioms CM31_sub
end PV_B2_FieldTotal
