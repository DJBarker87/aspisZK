import S9ActualCM31WrappingMapV1
import R22CanonicalCM31

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualCM31TotalCanonicalV1

theorem actual_cm_mul_total_canonical
    (x y : AspisR1S9ActualQMMulCutV1.field.CM31)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9ActualCM31WrappingMapV1.toProbeCM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9ActualCM31WrappingMapV1.toProbeCM y)) :
    ∃ z, AspisR1S9ActualQMMulCutV1.field.CM31.mul x y = .ok z ∧
      AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
        (AspisR1S9ActualCM31WrappingMapV1.toProbeCM z) := by
  have hwrap := AspisR1S9ActualCM31WrappingMapV1.actual_cm_mul_wrapping x y
  cases hcall : AspisR1S9ActualQMMulCutV1.field.CM31.mul x y with
  | ok z =>
      have hval : AspisR1S9ActualCM31WrappingMapV1.toProbeCM z =
          AspisR1.R22CanonicalCM31.wrappingCMMul
            (AspisR1S9ActualCM31WrappingMapV1.toProbeCM x)
            (AspisR1S9ActualCM31WrappingMapV1.toProbeCM y) := by
        simp only [hcall, bind_tc_ok] at hwrap
        exact Result.ok.inj hwrap
      refine ⟨z, rfl, ?_⟩
      rw [hval]
      exact AspisR1.R22CanonicalCM31.cm_mul_canonical
        (AspisR1S9ActualCM31WrappingMapV1.toProbeCM x)
        (AspisR1S9ActualCM31WrappingMapV1.toProbeCM y) hx hy
  | fail e =>
      simp only [hcall, bind_tc_fail] at hwrap
      cases hwrap
  | div =>
      simp only [hcall, bind_tc_div] at hwrap
      cases hwrap

#print axioms actual_cm_mul_total_canonical

end AspisR1S9ActualCM31TotalCanonicalV1
