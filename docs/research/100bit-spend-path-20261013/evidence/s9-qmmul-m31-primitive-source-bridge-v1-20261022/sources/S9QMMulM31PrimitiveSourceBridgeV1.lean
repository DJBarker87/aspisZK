import AspisR1S9ActualQMMulCutV1.Funs
import AspisR1S9WideMulM31CutV1.Funs
import AspisR1S9WideAddSourceBodyV1.Funs
import R22CanonicalM31AddSub

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMMulM31PrimitiveSourceBridgeV1

private abbrev Actual := AspisR1S9ActualQMMulCutV1.field.M31
private abbrev Scalar := AspisR1S9WideMulM31CutV1.field.M31
private abbrev P : Nat := AspisR1.ExtractedCurrentM31AddSub.P

/-- Std's generated wrapping primitive and the Aeneas UScalar wrapper have the
same U32 bitvector result. The bridge is proved from their value equations,
not by definitional equality. -/
private theorem u32_wrapping_add_eq_scalar (x y : Std.U32) :
    Std.U32.wrapping_add x y = UScalar.wrapping_add x y := by
  apply UScalar.eq_of_val_eq
  rw [Std.U32.wrapping_add_val_eq, UScalar.wrapping_add_val_eq]

private theorem u32_wrapping_sub_eq_scalar (x y : Std.U32) :
    Std.U32.wrapping_sub x y = UScalar.wrapping_sub x y := by
  apply UScalar.eq_of_val_eq
  rw [Std.U32.wrapping_sub_val_eq, UScalar.wrapping_sub_val_eq]

/-- The Q-multiplication cut's scalar multiply and reducer reduce to the same
Aeneas bodies as the already retained scalar-field cut. -/
theorem actual_reduce_eq_scalar (x : Std.U64) :
    AspisR1S9ActualQMMulCutV1.field.reduce_u64 x =
      AspisR1S9WideMulM31CutV1.field.reduce_u64 x := by
  unfold AspisR1S9ActualQMMulCutV1.field.reduce_u64
    AspisR1S9WideMulM31CutV1.field.reduce_u64
    AspisR1S9ActualQMMulCutV1.field.P
    AspisR1S9WideMulM31CutV1.field.P
  rfl

theorem actual_m31_mul_eq_scalar (x y : Actual) :
    AspisR1S9ActualQMMulCutV1.field.M31.mul x y =
      AspisR1S9WideMulM31CutV1.field.M31.mul x y := by
  unfold AspisR1S9ActualQMMulCutV1.field.M31.mul
    AspisR1S9WideMulM31CutV1.field.M31.mul
    AspisR1S9ActualQMMulCutV1.field.reduce_u64
    AspisR1S9WideMulM31CutV1.field.reduce_u64
    AspisR1S9ActualQMMulCutV1.field.P
    AspisR1S9WideMulM31CutV1.field.P
  rfl

/-- The newly emitted source body uses wrapping primitives directly. This is
the exact R22 wrapping expression; it is equal to the checked M31 source call
on canonical operands by the retained R22 theorem below. -/
theorem actual_m31_add_eq_r22_wrapping (x y : Actual) :
    AspisR1S9ActualQMMulCutV1.field.M31.add x y =
      Result.ok (AspisR1.R22CanonicalM31AddSub.wrappingAdd x y) := by
  unfold AspisR1S9ActualQMMulCutV1.field.M31.add
    AspisR1.R22CanonicalM31AddSub.wrappingAdd
    AspisR1.R22CanonicalM31AddSub.wrappingFinish
    AspisR1.R22CanonicalM31AddSub.sourceP
    AspisR1Qm31ArithmeticProbe.field.P
    AspisR1S9ActualQMMulCutV1.field.P
  simp only [lift, bind_tc_ok, u32_wrapping_add_eq_scalar]
  split_ifs <;> rfl

theorem actual_m31_sub_eq_r22_wrapping (x y : Actual) :
    AspisR1S9ActualQMMulCutV1.field.M31.sub x y =
      Result.ok (AspisR1.R22CanonicalM31AddSub.wrappingSub x y) := by
  unfold AspisR1S9ActualQMMulCutV1.field.M31.sub
    AspisR1.R22CanonicalM31AddSub.wrappingSub
    AspisR1.R22CanonicalM31AddSub.wrappingFinish
    AspisR1.R22CanonicalM31AddSub.sourceP
    AspisR1Qm31ArithmeticProbe.field.P
    AspisR1S9ActualQMMulCutV1.field.P
  simp only [lift, bind_tc_ok, u32_wrapping_add_eq_scalar,
    u32_wrapping_sub_eq_scalar]
  split_ifs <;> rfl

/-- Canonical-domain equality to the already-proved checked source body. -/
theorem actual_m31_add_eq_checked (x y : Actual)
    (hx : x.val < P) (hy : y.val < P) :
    AspisR1S9ActualQMMulCutV1.field.M31.add x y =
      AspisR1Qm31ArithmeticProbe.field.M31.add x y := by
  calc
    AspisR1S9ActualQMMulCutV1.field.M31.add x y =
        Result.ok (AspisR1.R22CanonicalM31AddSub.wrappingAdd x y) :=
      actual_m31_add_eq_r22_wrapping x y
    _ = AspisR1Qm31ArithmeticProbe.field.M31.add x y :=
      (AspisR1.R22CanonicalM31AddSub.canonical_add_agrees x y hx hy).symm

theorem actual_m31_sub_eq_checked (x y : Actual)
    (hx : x.val < P) (hy : y.val < P) :
    AspisR1S9ActualQMMulCutV1.field.M31.sub x y =
      AspisR1Qm31ArithmeticProbe.field.M31.sub x y := by
  calc
    AspisR1S9ActualQMMulCutV1.field.M31.sub x y =
        Result.ok (AspisR1.R22CanonicalM31AddSub.wrappingSub x y) :=
      actual_m31_sub_eq_r22_wrapping x y
    _ = AspisR1Qm31ArithmeticProbe.field.M31.sub x y :=
      (AspisR1.R22CanonicalM31AddSub.canonical_sub_agrees x y hx hy).symm

#print axioms u32_wrapping_add_eq_scalar
#print axioms u32_wrapping_sub_eq_scalar
#print axioms actual_reduce_eq_scalar
#print axioms actual_m31_mul_eq_scalar
#print axioms actual_m31_add_eq_r22_wrapping
#print axioms actual_m31_sub_eq_r22_wrapping
#print axioms actual_m31_add_eq_checked
#print axioms actual_m31_sub_eq_checked

end AspisR1S9QMMulM31PrimitiveSourceBridgeV1
