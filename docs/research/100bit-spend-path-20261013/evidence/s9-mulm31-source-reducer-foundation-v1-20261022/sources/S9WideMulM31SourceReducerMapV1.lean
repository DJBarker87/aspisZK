import S9WideMulM31SourceReducerV1
import S9WideMulM31SourceFoldMapV1
import R22CurrentReducerMul
import ExtractedCurrentReducer
import AspisV8R17.RawReducerNat

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideMulM31SourceReducerMapV1

private theorem u32_wrapping_sub_eq_scalar (x y : Std.U32) :
    Std.U32.wrapping_sub x y = UScalar.wrapping_sub x y := by
  apply UScalar.eq_of_val_eq
  rw [Std.U32.wrapping_sub_val_eq, UScalar.wrapping_sub_val_eq]

private theorem sourceP_value :
    AspisR1S9WideMulM31CutV1.field.P.val = AspisV8R17.RawReducer.P := by
  norm_num [AspisR1S9WideMulM31CutV1.field.P, AspisV8R17.RawReducer.P]

private theorem sourceP_eq_mask32 :
    AspisR1S9WideMulM31CutV1.field.P =
      AspisR1.ExtractedCurrentReducer.mask32 := by
  apply UScalar.eq_of_val_eq
  simpa only [AspisR1.ExtractedCurrentReducer.mask32_value] using sourceP_value

/-- The generated scalar-source reducer has the exact existing wrapping
reducer result, including the guarded final subtraction. -/
theorem source_reduce_u64_eq_R22_wrappingReduce (x : Std.U64) :
    AspisR1S9WideMulM31CutV1.field.reduce_u64 x =
      .ok (AspisR1.R22CurrentReducerMul.wrappingReduce x) := by
  rw [AspisR1S9WideMulM31SourceReducerV1.source_reduce_u64_eq_sourceWrappingReduce]
  apply congrArg Result.ok
  have hdouble :
      AspisR1S9WideMulM31SourceReducerV1.sourceWrappingFold
          (AspisR1S9WideMulM31SourceReducerV1.sourceWrappingFold x) =
        AspisR1.R22CurrentReducerMul.wrappingFold
          (AspisR1.R22CurrentReducerMul.wrappingFold x) := by
    calc
      _ = AspisR1.R22CurrentReducerMul.wrappingFold
            (AspisR1S9WideMulM31SourceReducerV1.sourceWrappingFold x) := by
              rw [AspisR1S9WideMulM31SourceFoldMapV1.sourceWrappingFold_eq_R22]
      _ = _ := by
            rw [AspisR1S9WideMulM31SourceFoldMapV1.sourceWrappingFold_eq_R22]
  unfold AspisR1S9WideMulM31SourceReducerV1.sourceWrappingReduce
    AspisR1.R22CurrentReducerMul.wrappingReduce
  rw [hdouble]
  let n : Std.U32 := UScalar.cast .U32
    (AspisR1.R22CurrentReducerMul.wrappingFold
      (AspisR1.R22CurrentReducerMul.wrappingFold x))
  have hcond : (n >= AspisR1S9WideMulM31CutV1.field.P) ↔
      AspisV8R17.RawReducer.P ≤ n.val := by
    change AspisR1S9WideMulM31CutV1.field.P.val ≤ n.val ↔
      AspisV8R17.RawReducer.P ≤ n.val
    rw [sourceP_value]
  change (if n >= AspisR1S9WideMulM31CutV1.field.P then
      Std.U32.wrapping_sub n AspisR1S9WideMulM31CutV1.field.P else n) =
    (if AspisV8R17.RawReducer.P ≤ n.val then
      UScalar.wrapping_sub n AspisR1.ExtractedCurrentReducer.mask32 else n)
  by_cases h : AspisV8R17.RawReducer.P ≤ n.val
  · rw [if_pos (hcond.mpr h), if_pos h, sourceP_eq_mask32]
    exact u32_wrapping_sub_eq_scalar n AspisR1.ExtractedCurrentReducer.mask32
  · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]

#print axioms source_reduce_u64_eq_R22_wrappingReduce

end AspisR1S9WideMulM31SourceReducerMapV1
