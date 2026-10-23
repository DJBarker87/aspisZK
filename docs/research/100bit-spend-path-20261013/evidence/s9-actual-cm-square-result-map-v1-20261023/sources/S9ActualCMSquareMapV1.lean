import AspisR1S9SquareMulQMCutV1.Funs
import S9ActualCMSquareGraphV1
import ExtractedMaskCM31Square
import ExtractedMaskM31AddSub
import ExtractedCurrentM31AddSub
import S9QMMulM31PrimitiveSourceBridgeV1
import S9ActualCM31WrappingMapV1
import S9WideMulM31ActualM31MapV1
import R22CurrentReducerMul
import R22CanonicalM31AddSub

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualCMSquareMapV1

abbrev ActualCM := AspisR1S9SquareMulQMCutV1.field.CM31
abbrev SelectedCM := AspisR1SelectedMaskProbe.field.CM31

def toSelectedCM (x : ActualCM) : SelectedCM := ⟨x.a, x.b⟩

private theorem actual_reduce_result (x : Std.U64) :
    AspisR1S9SquareMulQMCutV1.field.M31.reduce_u64 x =
      .ok (AspisR1.R22CurrentReducerMul.wrappingReduce x) := by
  have hbody :
      AspisR1S9SquareMulQMCutV1.field.M31.reduce_u64 x =
        AspisR1S9ActualQMMulCutV1.field.M31.reduce_u64 x := by
    unfold AspisR1S9SquareMulQMCutV1.field.M31.reduce_u64
      AspisR1S9ActualQMMulCutV1.field.M31.reduce_u64
      AspisR1S9SquareMulQMCutV1.field.reduce_u64
      AspisR1S9ActualQMMulCutV1.field.reduce_u64
      AspisR1S9SquareMulQMCutV1.field.P
      AspisR1S9ActualQMMulCutV1.field.P
    rfl
  rw [hbody]
  exact AspisR1S9ActualCM31WrappingMapV1.actual_reduce_wrapper_wrapping x

private theorem actual_mul_result (x y : Std.U32) :
    AspisR1S9SquareMulQMCutV1.field.M31.mul x y =
      .ok (AspisR1.R22CurrentReducerMul.wrappingMul x y) := by
  have hbody :
      AspisR1S9SquareMulQMCutV1.field.M31.mul x y =
        AspisR1S9WideMulM31CutV1.field.M31.mul x y := by
    unfold AspisR1S9SquareMulQMCutV1.field.M31.mul
      AspisR1S9WideMulM31CutV1.field.M31.mul
      AspisR1S9SquareMulQMCutV1.field.reduce_u64
      AspisR1S9WideMulM31CutV1.field.reduce_u64
      AspisR1S9SquareMulQMCutV1.field.P
      AspisR1S9WideMulM31CutV1.field.P
    rfl
  rw [hbody]
  exact AspisR1S9WideMulM31ActualM31MapV1.actual_m31_mul_eq_R22_wrappingMul x y

private theorem actual_add_result (x y : Std.U32) :
    AspisR1S9SquareMulQMCutV1.field.M31.add x y =
      .ok (AspisR1.R22CanonicalM31AddSub.wrappingAdd x y) := by
  have hbody :
      AspisR1S9SquareMulQMCutV1.field.M31.add x y =
        AspisR1S9ActualQMMulCutV1.field.M31.add x y := by
    unfold AspisR1S9SquareMulQMCutV1.field.M31.add
      AspisR1S9ActualQMMulCutV1.field.M31.add
      AspisR1S9SquareMulQMCutV1.field.P
      AspisR1S9ActualQMMulCutV1.field.P
    rfl
  rw [hbody]
  exact AspisR1S9QMMulM31PrimitiveSourceBridgeV1.actual_m31_add_eq_r22_wrapping x y

/-- The actual source's wrapping-square operand, reducer, multiply, and double
produce the same canonical formulas as the selected checked square. -/
theorem actual_square_words (x : ActualCM)
    (hx : x.a.val < 2147483647) (hy : x.b.val < 2147483647) :
    ∃ z : ActualCM,
      AspisR1S9SquareMulQMCutV1.field.CM31.square x = .ok z ∧
      z.a.val = ((x.a.val + x.b.val) *
        (x.a.val + 2147483647 - x.b.val)) % 2147483647 ∧
      z.b.val = ((x.a.val * x.b.val) % 2147483647 +
        (x.a.val * x.b.val) % 2147483647) % 2147483647 := by
  obtain ⟨product, hproduct, hvproduct⟩ :=
    AspisR1.ExtractedMaskCM31Square.squareOperand_success x.a x.b hx hy
  have hactualProduct :
      AspisR1S9ActualCMSquareOperandMapV1.actualSquareOperand x.a x.b = .ok product := by
    rw [AspisR1S9ActualCMSquareOperandMapV1.actual_square_operand_eq_selected x.a x.b hx hy]
    exact hproduct
  let real := AspisR1.R22CurrentReducerMul.wrappingReduce product
  let ab := AspisR1.R22CurrentReducerMul.wrappingMul x.a x.b
  let imag := AspisR1.R22CanonicalM31AddSub.wrappingAdd ab ab
  have hsource :
      AspisR1S9SquareMulQMCutV1.field.CM31.square x = .ok ⟨real, imag⟩ := by
    rw [AspisR1S9ActualCMSquareGraphV1.actual_cm_square_graph]
    simp only [hactualProduct, bind_tc_ok, actual_reduce_result,
      actual_mul_result, actual_add_result,
      AspisR1S9SquareMulQMCutV1.field.M31.double, bind_tc_ok,
      real, ab, imag]
  have hrealMod :=
    (AspisR1.R22CurrentReducerMul.wrapping_reduce_mod product).1
  have habMod :=
    (AspisR1.R22CurrentReducerMul.wrapping_mul_mod x.a x.b).1
  have habCan :=
    (AspisR1.R22CurrentReducerMul.wrapping_mul_mod x.a x.b).2
  have himagMod : imag.val = (ab.val + ab.val) % 2147483647 := by
    have habCanSelected : ab.val < AspisR1.ExtractedMaskM31AddSub.P := by
      simpa only [AspisR1.ExtractedMaskM31AddSub.P] using habCan
    have habCanCurrent :
        ab.val < AspisR1.ExtractedCurrentM31AddSub.P := by
      simpa only [AspisR1.ExtractedCurrentM31AddSub.P] using habCan
    obtain ⟨s, hs, hvs, _hsc⟩ :=
      AspisR1.ExtractedCurrentM31AddSub.current_add_mod ab ab
        habCanCurrent habCanCurrent
    have hwrap := AspisR1.R22CanonicalM31AddSub.canonical_add_agrees ab ab
      habCanCurrent habCanCurrent
    have hvalEq : AspisR1.R22CanonicalM31AddSub.wrappingAdd ab ab = s :=
      Result.ok.inj (hwrap.symm.trans hs)
    dsimp [imag, ab]
    exact congrArg (fun q : Std.U32 => q.val) hvalEq |>.trans hvs
  refine ⟨⟨real, imag⟩, hsource, ?_, ?_⟩
  · calc
      real.val = product.val % 2147483647 := by
        simpa only [real, AspisV8R17.RawReducer.P] using hrealMod
      _ = ((x.a.val + x.b.val) *
          (x.a.val + 2147483647 - x.b.val)) % 2147483647 := by
        rw [hvproduct]
  · calc
      imag.val = (ab.val + ab.val) % 2147483647 := himagMod
      _ = (x.a.val * x.b.val % 2147483647 +
          x.a.val * x.b.val % 2147483647) % 2147483647 := by
        rw [habMod]

/-- The same actual source call maps to the selected checked CM31.square call
for canonical coordinates; its success is derived from the source graph. -/
theorem actual_square_maps_to_selected (x : ActualCM)
    (hx : x.a.val < 2147483647) (hy : x.b.val < 2147483647) :
    (do
      let z ← AspisR1S9SquareMulQMCutV1.field.CM31.square x
      Result.ok (toSelectedCM z)) =
      AspisR1SelectedMaskProbe.field.CM31.square (toSelectedCM x) := by
  obtain ⟨z, hz, hza, hzb⟩ := actual_square_words x hx hy
  obtain ⟨w, hw, _hwcan, hwa, hwb⟩ :=
    AspisR1.ExtractedMaskCM31Square.current_square_words (toSelectedCM x)
      ⟨hx, hy⟩
  have hza' : z.a.val = w.a.val := by
    rw [hza, hwa]
    rfl
  have hzb' : z.b.val = w.b.val := by
    rw [hzb, hwb]
    rfl
  have hzw : toSelectedCM z = w := by
    cases z with
    | mk za zb =>
      cases w with
      | mk wa wb =>
        simp only [toSelectedCM, AspisR1SelectedMaskProbe.field.CM31.mk.injEq]
        exact ⟨UScalar.val_eq_imp za wa hza', UScalar.val_eq_imp zb wb hzb'⟩
  rw [hz, hw]
  simp only [bind_tc_ok, hzw]

#print axioms actual_square_words
#print axioms actual_square_maps_to_selected

end AspisR1S9ActualCMSquareMapV1
