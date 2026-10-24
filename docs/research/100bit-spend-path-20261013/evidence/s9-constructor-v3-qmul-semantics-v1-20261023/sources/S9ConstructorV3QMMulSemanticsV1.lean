import S9ConstructorV3QMMulCanonicalV1
import S9ActualQM31CanonicalCheckedMapV1
import ExtractedCurrentQM31Exact

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ConstructorV3QMMulSemanticsV1

abbrev SourceQM := AspisR1S9ConstructorV3QMMulCanonicalV1.SourceQM
abbrev toActualQM := AspisR1S9ConstructorV3QMMulCanonicalV1.toActualQM
abbrev toProbe := AspisR1S9ConstructorV3QMMulCanonicalV1.toProbe
abbrev Can (x : SourceQM) :=
  AspisR1.ExtractedCurrentTowerAdd.CanonicalQM (toProbe x)
abbrev decode (x : SourceQM) := AspisR1.ExtractedCurrentQM31Exact.decode (toProbe x)

/-- Decoded multiplication for this same accepted constructor primitive call.
The proof reuses the existing exact tower and canonical wrapping/checked map. -/
theorem generated_mul_success_exact
    (x y z : SourceQM) (hx : Can x) (hy : Can y)
    (hcall : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul x y = .ok z) :
    Can z ∧ decode z = decode x * decode y := by
  have hmap := AspisR1S9ConstructorV3QMMulCanonicalV1.generated_mul_maps_to_cut x y
  rw [hcall] at hmap
  have hcut : AspisR1S9ActualQMMulCutV1.field.QM31.mul (toActualQM x) (toActualQM y) =
      .ok (toActualQM z) := hmap.symm
  have hchecked := AspisR1S9ActualQM31CanonicalCheckedMapV1.actual_qm_mul_eq_checked
    (toActualQM x) (toActualQM y) hx hy
  rw [hcut] at hchecked
  have hprobe : AspisR1Qm31ArithmeticProbe.field.QM31.mul (toProbe x) (toProbe y) =
      .ok (toProbe z) := hchecked.symm
  obtain ⟨out, hout, hcan, hdecode⟩ :=
    AspisR1.ExtractedCurrentQM31Exact.current_qm_mul_exact (toProbe x) (toProbe y) hx hy
  have heq : out = toProbe z := Result.ok.inj (hout.symm.trans hprobe)
  subst out
  exact ⟨hcan, hdecode⟩

#print axioms generated_mul_success_exact
end AspisR1S9ConstructorV3QMMulSemanticsV1
