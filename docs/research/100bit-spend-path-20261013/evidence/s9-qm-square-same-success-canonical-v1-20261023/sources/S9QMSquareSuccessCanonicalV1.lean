import S9ActualCMSquareMapV1
import S9QMSquareCombinedProbeOpsV1
import ExtractedCurrentTowerAdd

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMSquareSuccessCanonicalV1

abbrev SCM := AspisR1S9SquareMulQMCutV1.field.CM31

theorem cm_square_success_canonical (x z : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe x))
    (hz : AspisR1S9SquareMulQMCutV1.field.CM31.square x = .ok z) :
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe z) := by
  have hxa : x.a.val < 2147483647 := by
    simpa only [AspisR1S9QMSquareCombinedProbeOpsV1.toProbe,
      AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
      AspisR1.ExtractedCurrentTowerAdd.P,
      AspisR1.ExtractedCurrentM31AddSub.P] using hx.1
  have hxb : x.b.val < 2147483647 := by
    simpa only [AspisR1S9QMSquareCombinedProbeOpsV1.toProbe,
      AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
      AspisR1.ExtractedCurrentTowerAdd.P,
      AspisR1.ExtractedCurrentM31AddSub.P] using hx.2
  obtain ⟨w, hw, hwa, hwb⟩ :=
    AspisR1S9ActualCMSquareMapV1.actual_square_words x hxa hxb
  have hwz : w = z := Result.ok.inj (hw.symm.trans hz)
  subst z
  constructor
  · change w.a.val < AspisR1.ExtractedCurrentTowerAdd.P
    rw [hwa]
    exact Nat.mod_lt _ (by decide)
  · change w.b.val < AspisR1.ExtractedCurrentTowerAdd.P
    rw [hwb]
    exact Nat.mod_lt _ (by decide)

theorem by_r_success_canonical (x z : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe x))
    (hz : AspisR1S9SquareMulQMCutV1.field.mul_by_r x = .ok z) :
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe z) := by
  have hmap :=
    AspisR1S9QMSquareCombinedProbeOpsV1.combined_by_r_maps_to_probe x hx
  rw [hz] at hmap
  rw [AspisR1.R22CanonicalQM31.byR_agrees
    (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe x) hx] at hmap
  have hout : AspisR1S9QMSquareCombinedProbeOpsV1.toProbe z =
      AspisR1.R22CanonicalQM31.wrappingByR
        (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe x) :=
    Result.ok.inj hmap
  rw [hout]
  exact AspisR1.R22CanonicalQM31.byR_canonical _ hx

theorem cm_mul_success_canonical (x y z : SCM)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe y))
    (hz : AspisR1S9SquareMulQMCutV1.field.CM31.mul x y = .ok z) :
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM
      (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe z) := by
  have hmap :=
    AspisR1S9QMSquareCombinedProbeOpsV1.combined_cm_mul_maps_to_probe x y hx hy
  rw [hz] at hmap
  rw [AspisR1.R22CanonicalCM31.cm_mul_agrees
    (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe x)
    (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe y) hx hy] at hmap
  have hout : AspisR1S9QMSquareCombinedProbeOpsV1.toProbe z =
      AspisR1.R22CanonicalCM31.wrappingCMMul
        (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe x)
        (AspisR1S9QMSquareCombinedProbeOpsV1.toProbe y) :=
    Result.ok.inj hmap
  rw [hout]
  exact AspisR1.R22CanonicalCM31.cm_mul_canonical _ _ hx hy

#print axioms cm_square_success_canonical
#print axioms by_r_success_canonical
#print axioms cm_mul_success_canonical

end AspisR1S9QMSquareSuccessCanonicalV1
