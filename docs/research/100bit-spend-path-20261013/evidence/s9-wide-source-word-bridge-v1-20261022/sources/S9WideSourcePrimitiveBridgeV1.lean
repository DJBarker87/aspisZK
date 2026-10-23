import AspisR1S9ActualWideMulCutV1.Funs
import AspisR1S9ActualQMMulCutV1.Funs
import S9QMMulM31PrimitiveSourceBridgeV1
import R22CanonicalM31AddSub

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace AspisR1S9WideSourcePrimitiveBridgeV1

theorem wide_reduce_u64_eq_qcut (x : Std.U64) :
    AspisR1S9ActualWideMulCutV1.field.reduce_u64 x =
      AspisR1S9ActualQMMulCutV1.field.reduce_u64 x := by
  unfold AspisR1S9ActualWideMulCutV1.field.reduce_u64
    AspisR1S9ActualQMMulCutV1.field.reduce_u64
    AspisR1S9ActualWideMulCutV1.field.P
    AspisR1S9ActualQMMulCutV1.field.P
  rfl

theorem wide_m31_add_eq_qcut (x y : Std.U32) :
    AspisR1S9ActualWideMulCutV1.field.M31.add x y =
      AspisR1S9ActualQMMulCutV1.field.M31.add x y := by
  unfold AspisR1S9ActualWideMulCutV1.field.M31.add
    AspisR1S9ActualQMMulCutV1.field.M31.add
    AspisR1S9ActualWideMulCutV1.field.P
    AspisR1S9ActualQMMulCutV1.field.P
  rfl

theorem wide_m31_sub_eq_qcut (x y : Std.U32) :
    AspisR1S9ActualWideMulCutV1.field.M31.sub x y =
      AspisR1S9ActualQMMulCutV1.field.M31.sub x y := by
  unfold AspisR1S9ActualWideMulCutV1.field.M31.sub
    AspisR1S9ActualQMMulCutV1.field.M31.sub
    AspisR1S9ActualWideMulCutV1.field.P
    AspisR1S9ActualQMMulCutV1.field.P
  rfl

theorem wide_m31_mul_eq_qcut (x y : Std.U32) :
    AspisR1S9ActualWideMulCutV1.field.M31.mul x y =
      AspisR1S9ActualQMMulCutV1.field.M31.mul x y := by
  unfold AspisR1S9ActualWideMulCutV1.field.M31.mul
    AspisR1S9ActualQMMulCutV1.field.M31.mul
    AspisR1S9ActualWideMulCutV1.field.reduce_u64
    AspisR1S9ActualQMMulCutV1.field.reduce_u64
    AspisR1S9ActualWideMulCutV1.field.P
    AspisR1S9ActualQMMulCutV1.field.P
  rfl

theorem wide_m31_double_eq_qcut (x : Std.U32) :
    AspisR1S9ActualWideMulCutV1.field.M31.double x =
      AspisR1S9ActualQMMulCutV1.field.M31.double x := by
  unfold AspisR1S9ActualWideMulCutV1.field.M31.double
    AspisR1S9ActualQMMulCutV1.field.M31.double
    AspisR1S9ActualWideMulCutV1.field.M31.add
    AspisR1S9ActualQMMulCutV1.field.M31.add
    AspisR1S9ActualWideMulCutV1.field.P
    AspisR1S9ActualQMMulCutV1.field.P
  rfl

theorem wide_m31_double_canonical (x : Std.U32)
    (hx : x.val < AspisR1.R22CanonicalM31AddSub.P) :
    ∃ z, AspisR1S9ActualWideMulCutV1.field.M31.double x = .ok z ∧
      z.val < AspisR1.R22CanonicalM31AddSub.P := by
  refine ⟨AspisR1.R22CanonicalM31AddSub.wrappingAdd x x, ?_,
    AspisR1.R22CanonicalM31AddSub.wrapping_add_canonical x x hx hx⟩
  rw [wide_m31_double_eq_qcut]
  unfold AspisR1S9ActualQMMulCutV1.field.M31.double
  rw [AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_add_eq_checked
    x x hx hx]
  rw [AspisR1.R22CanonicalM31AddSub.canonical_add_agrees x x hx hx]

#print axioms wide_reduce_u64_eq_qcut
#print axioms wide_m31_add_eq_qcut
#print axioms wide_m31_sub_eq_qcut
#print axioms wide_m31_mul_eq_qcut
#print axioms wide_m31_double_eq_qcut
#print axioms wide_m31_double_canonical

end AspisR1S9WideSourcePrimitiveBridgeV1
