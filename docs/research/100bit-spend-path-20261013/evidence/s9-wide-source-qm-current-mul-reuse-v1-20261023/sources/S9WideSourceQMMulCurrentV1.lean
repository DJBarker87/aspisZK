import S9WideSourceQMCurrentOpsV1
import S9CombinedQMToCurrentV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9WideSourceQMMulCurrentV1
abbrev Q := AspisR1S9ActualQMMulCutV1.field.QM31
abbrev C := AspisR1CurrentWide.field.QM31
abbrev qToCurrent := AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9ActualQMCurrentHelperMapV1.mapResult f r

/-- Reuse the already-proved actual QM-to-Current bridge at this operation owner. -/
theorem qcut_qm_mul_maps_to_current (x y : Q)
    (hx : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM x))
    (hy : AspisR1.ExtractedCurrentTowerAdd.CanonicalQM
      (AspisR1S9ActualQM31WrappingMapV1.toProbeQM y)) :
    mapResult qToCurrent (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y) =
      AspisR1CurrentWide.field.QM31.mul (qToCurrent x) (qToCurrent y) := by
  have hhead : ∀ r : Result Q,
      mapResult qToCurrent r = AspisR1S9SourceResultTransportV1.mapResult
        AspisR1S9ActualQMCurrentHelperMapV1.actualToCurrent r := by
    intro r
    cases r <;> rfl
  exact (hhead (AspisR1S9ActualQMMulCutV1.field.QM31.mul x y)).trans
    (AspisR1S9CombinedQMToCurrentV1.actual_qm_mul_to_current x y hx hy)
#print axioms qcut_qm_mul_maps_to_current
end AspisR1S9WideSourceQMMulCurrentV1
