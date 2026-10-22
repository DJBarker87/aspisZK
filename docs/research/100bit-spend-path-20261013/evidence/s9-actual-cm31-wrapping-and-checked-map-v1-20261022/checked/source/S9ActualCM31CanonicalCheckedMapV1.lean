import S9ActualCM31WrappingMapV1
import R22CanonicalCM31

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualCM31CanonicalCheckedMapV1

theorem actual_cm_mul_eq_checked
    (x y : AspisR1S9ActualQMMulCutV1.field.CM31)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9ActualCM31WrappingMapV1.toProbeCM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9ActualCM31WrappingMapV1.toProbeCM y)) :
    (do
      let z ← AspisR1S9ActualQMMulCutV1.field.CM31.mul x y
      .ok (AspisR1S9ActualCM31WrappingMapV1.toProbeCM z)) =
      AspisR1Qm31ArithmeticProbe.field.CM31.mul
        (AspisR1S9ActualCM31WrappingMapV1.toProbeCM x)
        (AspisR1S9ActualCM31WrappingMapV1.toProbeCM y) := by
  calc
    (do
      let z ← AspisR1S9ActualQMMulCutV1.field.CM31.mul x y
      .ok (AspisR1S9ActualCM31WrappingMapV1.toProbeCM z)) =
        .ok (AspisR1.R22CanonicalCM31.wrappingCMMul
          (AspisR1S9ActualCM31WrappingMapV1.toProbeCM x)
          (AspisR1S9ActualCM31WrappingMapV1.toProbeCM y)) :=
      AspisR1S9ActualCM31WrappingMapV1.actual_cm_mul_wrapping x y
    _ = AspisR1Qm31ArithmeticProbe.field.CM31.mul
        (AspisR1S9ActualCM31WrappingMapV1.toProbeCM x)
        (AspisR1S9ActualCM31WrappingMapV1.toProbeCM y) :=
      (AspisR1.R22CanonicalCM31.cm_mul_agrees
        (AspisR1S9ActualCM31WrappingMapV1.toProbeCM x)
        (AspisR1S9ActualCM31WrappingMapV1.toProbeCM y) hx hy).symm

#print axioms actual_cm_mul_eq_checked

end AspisR1S9ActualCM31CanonicalCheckedMapV1
