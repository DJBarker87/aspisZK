import AspisR1S9ActualQMMulCutV1.Funs
import AspisR1S9WideMulM31CutV1.Funs
import S9QMMulM31PrimitiveSourceBridgeV1
import S9ActualCM31CrossGraphV1
import S9WideMulM31SourceReducerMapV1
import S9WideMulM31ActualM31MapV1
import R22CanonicalCM31
import R22CurrentReducerMul
import R22CanonicalM31AddSub

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualCM31WrappingMapV1

def toProbeCM (x : AspisR1S9ActualQMMulCutV1.field.CM31) :
    AspisR1Qm31ArithmeticProbe.field.CM31 := ⟨x.a, x.b⟩

theorem actual_reduce_wrapper_wrapping (x : Std.U64) :
    AspisR1S9ActualQMMulCutV1.field.M31.reduce_u64 x =
      .ok (AspisR1.R22CurrentReducerMul.wrappingReduce x) := by
  unfold AspisR1S9ActualQMMulCutV1.field.M31.reduce_u64
  simp only [bind_tc_ok,
    AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_reduce_eq_scalar,
    AspisR1S9WideMulM31SourceReducerMapV1.source_reduce_u64_eq_R22_wrappingReduce]

theorem actual_cm_mul_wrapping
    (x y : AspisR1S9ActualQMMulCutV1.field.CM31) :
    (do
      let z ← AspisR1S9ActualQMMulCutV1.field.CM31.mul x y
      .ok (toProbeCM z)) =
      .ok (AspisR1.R22CanonicalCM31.wrappingCMMul (toProbeCM x) (toProbeCM y)) := by
  rw [AspisR1S9ActualCM31CrossGraphV1.actual_cm_mul_graph]
  simp only [AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_mul_eq_scalar,
    AspisR1S9WideMulM31ActualM31MapV1.actual_m31_mul_eq_R22_wrappingMul,
    AspisR1S9ActualCM31CrossGraphV1.actual_cross_wrapping,
    actual_reduce_wrapper_wrapping,
    AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_sub_eq_r22_wrapping,
    bind_tc_ok, toProbeCM]
  rfl

#print axioms actual_reduce_wrapper_wrapping
#print axioms actual_cm_mul_wrapping

end AspisR1S9ActualCM31WrappingMapV1
