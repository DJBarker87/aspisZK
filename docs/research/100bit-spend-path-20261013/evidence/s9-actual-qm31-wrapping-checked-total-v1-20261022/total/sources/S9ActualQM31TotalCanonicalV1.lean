import S9ActualQM31WrappingMapV1
import R22CanonicalQM31

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualQM31TotalCanonicalV1

theorem actual_qm_mul_total_canonical
    (x y : AspisR1S9ActualQMMulCutV1.field.QM31)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y)) :
    ∃ z, AspisR1S9ActualQMMulCutV1.field.QM31.mul x y = .ok z ∧
      AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM z) := by
  have hwrap := AspisR1S9ActualQM31WrappingMapV1.actual_qm_mul_wrapping x y
  cases hcall : AspisR1S9ActualQMMulCutV1.field.QM31.mul x y with
  | ok z =>
      have hval : AspisR1S9ActualQM31WrappingMapV1.toProbeQM z =
          AspisR1.R22CanonicalQM31.wrappingQMMul
            (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)
            (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y) := by
        simp only [hcall, bind_tc_ok] at hwrap
        exact Result.ok.inj hwrap
      refine ⟨z, rfl, ?_⟩
      rw [hval]
      exact AspisR1.R22CanonicalQM31.qm_mul_canonical
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x)
        (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y) hx hy
  | fail e =>
      simp only [hcall, bind_tc_fail] at hwrap
      cases hwrap
  | div =>
      simp only [hcall, bind_tc_div] at hwrap
      cases hwrap

#print axioms actual_qm_mul_total_canonical

end AspisR1S9ActualQM31TotalCanonicalV1
