import R1Z.PV_B2_W_13_CM31_mul
import R1Z.PV_B2_Total_CM31_sub
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.CM31.mul
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  aspis_core.field.CM31
  :=
  let m0 := aspis_core.field.M31.mul self.a rhs.a
  let m1 := aspis_core.field.M31.mul self.b rhs.b
  let i := self.a
  let i1 := (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 := (core.convert.num.FromU64U32.from i2)
  let i4 := (Std.U64.wrapping_add i1 i3)
  let i5 := rhs.a
  let i6 := (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 := (core.convert.num.FromU64U32.from i7)
  let i9 := (Std.U64.wrapping_add i6 i8)
  let i10 := (Std.U64.wrapping_mul i4 i9)
  let m2 := aspis_core.field.M31.reduce_u64 i10
  let m := aspis_core.field.M31.sub m0 m1
  let m3 := aspis_core.field.M31.sub m2 m0
  let m4 := aspis_core.field.M31.sub m3 m1
  { a := m, b := m4 }
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem CM31_mul (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) : PV_B2_WeightsNative.aspis_core.field.CM31.mul self rhs = ok (PV_B2_FieldValue.aspis_core.field.CM31.mul self rhs) := by
  unfold PV_B2_WeightsNative.aspis_core.field.CM31.mul PV_B2_FieldValue.aspis_core.field.CM31.mul
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul, PV_B2_FieldTotal.M31_reduce_u64, PV_B2_FieldTotal.M31_add, PV_B2_FieldTotal.M31_double, PV_B2_FieldTotal.CM31_add, PV_B2_FieldTotal.M31_sub, PV_B2_FieldTotal.CM31_sub,lift,bind_tc_ok]
#print axioms CM31_mul
end PV_B2_FieldTotal
