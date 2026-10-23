import S9ActualCMSquareMapV1
import S9QMSquareCombinedSelectedOpsV1
import S9QMSquareSuccessBindMapV1
import ExtractedMaskQM31SquareExact

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9QMSquareSourceResultHeadV1

abbrev SCM := AspisR1S9SquareMulQMCutV1.field.CM31
abbrev TCM := AspisR1SelectedMaskProbe.field.CM31
abbrev mapResult {A B : Type} (f : A → B) (r : Result A) :=
  AspisR1S9QMSquareSuccessBindMapV1.mapResult f r
abbrev combinedToSelected := AspisR1S9QMSquareCombinedSelectedOpsV1.toSelected
abbrev actualToSelected := AspisR1S9ActualCMSquareMapV1.toSelectedCM

private theorem selected_map_eq_actual_map :
    combinedToSelected = actualToSelected := by
  funext x
  cases x with
  | mk a b => rfl

/-- The source square statement is converted to the exact result-map form
used by the outer bind transport, without forcing the square body to reduce. -/
theorem actual_square_result_maps_to_selected (x : SCM)
    (ha : x.a.val < 2147483647) (hb : x.b.val < 2147483647) :
    mapResult combinedToSelected
      (AspisR1S9SquareMulQMCutV1.field.CM31.square x) =
      AspisR1SelectedMaskProbe.field.CM31.square (combinedToSelected x) := by
  have hsource :=
    AspisR1S9ActualCMSquareMapV1.actual_square_maps_to_selected x ha hb
  calc
    mapResult combinedToSelected
        (AspisR1S9SquareMulQMCutV1.field.CM31.square x) =
      (do
        let z ← AspisR1S9SquareMulQMCutV1.field.CM31.square x
        Result.ok (combinedToSelected z)) := by
          exact AspisR1S9SourceResultTransportV1.mapResult_eq_bind _ _
    _ = AspisR1SelectedMaskProbe.field.CM31.square (combinedToSelected x) := by
          simpa only [selected_map_eq_actual_map] using hsource

#print axioms actual_square_result_maps_to_selected

end AspisR1S9QMSquareSourceResultHeadV1
