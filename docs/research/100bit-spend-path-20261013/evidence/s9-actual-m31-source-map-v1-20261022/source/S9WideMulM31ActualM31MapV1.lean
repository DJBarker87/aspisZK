import AspisR1S9WideMulM31CutV1.Funs
import S9U64ScalarCompatibilityV1
import S9WideMulM31SourceReducerMapV1
import R22CurrentReducerMul

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideMulM31ActualM31MapV1

/-- The actual extracted M31 multiplication body returns the existing R22
wrapping multiplication expression for every input word. -/
theorem actual_m31_mul_eq_R22_wrappingMul (x y : Std.U32) :
    AspisR1S9WideMulM31CutV1.field.M31.mul x y =
      .ok (AspisR1.R22CurrentReducerMul.wrappingMul x y) := by
  simp only [AspisR1S9WideMulM31CutV1.field.M31.mul,

    lift, bind_tc_ok]
  rw [AspisR1S9U64ScalarCompatibilityV1.u64_wrapping_mul_eq_uscalar,
    AspisR1S9WideMulM31SourceReducerMapV1.source_reduce_u64_eq_R22_wrappingReduce]
  rfl

#print axioms actual_m31_mul_eq_R22_wrappingMul

end AspisR1S9WideMulM31ActualM31MapV1
