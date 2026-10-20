import S3PairLowCallStepBridgeV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1PairLowCallCut

theorem actual_wide_mul_maps_to_s
    (x y : field.WideExact) :
    (do
      let z ← actualFieldOps.wideMul x y
      .ok (toActualS z)) =
      AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.mul
        (toActualS x) (toActualS y) := by
  unfold actualFieldOps LowFieldOps.wideMul
  simp only [to_from_actual]
  cases h : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.mul
      (toActualS x) (toActualS y) <;> simp [h, to_from_actual]

theorem actual_wide_mul_m31_maps_to_s
    (x : field.WideExact) (s : field.M31) :
    (do
      let z ← actualFieldOps.wideMulM31 x s
      .ok (toActualS z)) =
      AspisR1S3PowersLowEntryCanonicalV1.mulM31 (toActualS x) s := by
  unfold actualFieldOps LowFieldOps.wideMulM31
  simp only [to_from_actual]
  cases h : AspisR1S3PowersLowEntryCanonicalV1.mulM31 (toActualS x) s <;>
    simp [h, to_from_actual]

#print axioms actual_wide_mul_maps_to_s
#print axioms actual_wide_mul_m31_maps_to_s

end AspisR1PairLowCallCut
