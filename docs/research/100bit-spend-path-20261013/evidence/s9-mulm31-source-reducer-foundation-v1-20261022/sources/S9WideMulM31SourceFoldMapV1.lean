import S9WideMulM31SourceReducerV1
import S9WideMulM31ShiftBridgeV1
import S9U64ScalarCompatibilityV1
import R22CurrentReducerMul
import ExtractedCurrentReducer

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideMulM31SourceFoldMapV1

private theorem sourceMask_eq_R22Mask :
    UScalar.cast .U64 AspisR1S9WideMulM31CutV1.field.P =
      AspisR1.ExtractedCurrentReducer.mask64 := by
  have hp : AspisR1S9WideMulM31CutV1.field.P.val = AspisV8R17.RawReducer.P := by
    norm_num [AspisR1S9WideMulM31CutV1.field.P, AspisV8R17.RawReducer.P]
  have hp32 : AspisR1S9WideMulM31CutV1.field.P =
      AspisR1.ExtractedCurrentReducer.mask32 := by
    apply UScalar.eq_of_val_eq
    simpa only [AspisR1.ExtractedCurrentReducer.mask32_value] using hp
  rw [hp32, AspisR1.ExtractedCurrentReducer.mask64]

theorem sourceWrappingFold_eq_R22 (x : Std.U64) :
    AspisR1S9WideMulM31SourceReducerV1.sourceWrappingFold x =
      AspisR1.R22CurrentReducerMul.wrappingFold x := by
  unfold AspisR1S9WideMulM31SourceReducerV1.sourceWrappingFold
    AspisR1.R22CurrentReducerMul.wrappingFold
  calc
    _ = UScalar.wrapping_add
        (UScalar.and x (UScalar.cast .U64 AspisR1S9WideMulM31CutV1.field.P))
        (Std.U64.wrapping_shr x 31#u32) := by
          rw [AspisR1S9U64ScalarCompatibilityV1.u64_wrapping_add_eq_uscalar,
            AspisR1S9U64ScalarCompatibilityV1.u64_and_eq_uscalar]
    _ = UScalar.wrapping_add
        (UScalar.and x AspisR1.ExtractedCurrentReducer.mask64)
        (AspisR1.R22CurrentReducerMul.high x) := by
          rw [sourceMask_eq_R22Mask,
            AspisR1S9WideMulM31ShiftBridgeV1.wrapping_shr31_eq_bitvector]
          rfl
    _ = _ := rfl

#print axioms sourceWrappingFold_eq_R22

end AspisR1S9WideMulM31SourceFoldMapV1
