import S9ActualQM31WrappingMapV1
import R22CanonicalQM31

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualQM31CanonicalCheckedMapV1

theorem actual_qm_mul_eq_checked
    (x y : AspisR1S9ActualQMMulCutV1.field.QM31)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y)) :
    (do
      let z ← AspisR1S9ActualQMMulCutV1.field.QM31.mul x y
      .ok (AspisR1S9ActualQM31WrappingMapV1.toProbeQM z)) =
      AspisR1Qm31ArithmeticProbe.field.QM31.mul
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y) := by
  calc
    (do
      let z ← AspisR1S9ActualQMMulCutV1.field.QM31.mul x y
      .ok (AspisR1S9ActualQM31WrappingMapV1.toProbeQM z)) =
        .ok (AspisR1.R22CanonicalQM31.wrappingQMMul
          (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)
          (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y)) :=
      AspisR1S9ActualQM31WrappingMapV1.actual_qm_mul_wrapping x y
    _ = AspisR1Qm31ArithmeticProbe.field.QM31.mul
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y) :=
      (AspisR1.R22CanonicalQM31.qm_mul_agrees
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y) hx hy).symm

#print axioms actual_qm_mul_eq_checked

end AspisR1S9ActualQM31CanonicalCheckedMapV1
