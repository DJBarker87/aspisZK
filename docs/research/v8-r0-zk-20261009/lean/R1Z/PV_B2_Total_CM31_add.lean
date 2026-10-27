import R1Z.PV_B2_W_10_CM31_add
import R1Z.PV_B2_Total_M31_double
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.CM31.add
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  aspis_core.field.CM31
  :=
  let m := aspis_core.field.M31.add self.a rhs.a
  let m1 := aspis_core.field.M31.add self.b rhs.b
  { a := m, b := m1 }
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem CM31_add (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) : PV_B2_WeightsNative.aspis_core.field.CM31.add self rhs = ok (PV_B2_FieldValue.aspis_core.field.CM31.add self rhs) := by
  unfold PV_B2_WeightsNative.aspis_core.field.CM31.add PV_B2_FieldValue.aspis_core.field.CM31.add
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul, PV_B2_FieldTotal.M31_reduce_u64, PV_B2_FieldTotal.M31_add, PV_B2_FieldTotal.M31_double,lift,bind_tc_ok]
#print axioms CM31_add
end PV_B2_FieldTotal
