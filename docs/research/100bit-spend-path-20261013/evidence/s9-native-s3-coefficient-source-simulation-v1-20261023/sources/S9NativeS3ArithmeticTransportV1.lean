import S9NativeS3FieldReaderV1
import S9NativeWideDecodedArithmeticV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9NativeS3ArithmeticTransportV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeS3FieldReaderV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical

theorem native_add_success_old_operation (x y out : W) (hx : Can x) (hy : Can y)
    (h : aspis_core.field.wide_exact.WideExact.add x y=.ok out) :
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.add
      (nativeToOld x) (nativeToOld y)=.ok (nativeToOld out) := by
  unfold AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.add
  rw [native_current_coordinates,native_current_coordinates]
  have hm := AspisR1S9ActualPairWideAddCurrentV1.actual_wide_add_maps_current x y hx hy
  rw [h] at hm
  have hc : AspisR1CurrentWide.field.wide_exact.WideExact.add
      (AspisR1S9ActualPairWideCanonicalV1.toCurrent x)
      (AspisR1S9ActualPairWideCanonicalV1.toCurrent y)=
      .ok (AspisR1S9ActualPairWideCanonicalV1.toCurrent out) := hm.symm
  simp only [hc,bind_tc_ok] <;> rfl

theorem native_mul_success_old_operation (x y out : W) (hx : Can x) (hy : Can y)
    (h : aspis_core.field.wide_exact.WideExact.mul x y=.ok out) :
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.mul
      (nativeToOld x) (nativeToOld y)=.ok (nativeToOld out) := by
  unfold AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.mul
  rw [native_current_coordinates,native_current_coordinates]
  have hm := AspisR1S9ActualPairWideCanonicalV1.actual_wide_mul_maps_current x y hx hy
  rw [h] at hm
  have hc : AspisR1CurrentWide.field.wide_exact.WideExact.mul
      (AspisR1S9ActualPairWideCanonicalV1.toCurrent x)
      (AspisR1S9ActualPairWideCanonicalV1.toCurrent y)=
      .ok (AspisR1S9ActualPairWideCanonicalV1.toCurrent out) := hm.symm
  simp only [hc,bind_tc_ok] <;> rfl

#print axioms native_add_success_old_operation
#print axioms native_mul_success_old_operation
end AspisR1S9NativeS3ArithmeticTransportV1
