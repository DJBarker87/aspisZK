import S9ActualWeightsFieldOwnedMapV1
import S9OwnedFieldCanonicalV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9ActualFieldSuccessCanonicalV1

/-- Success of the exact attempt7 field body transfers at the same byte slice
and index to the owned reader, then reuses its checked canonicality result. -/
theorem actual_field_success_canonical
    (bytes : Slice U8) (i : Usize)
    (out : AspisR1S9ActualFieldTypesCutV1.field.wide_exact.WideExact)
    (h : AspisR1S9ActualFieldTypesCutV1.weights.field bytes i = .ok out) :
    AspisR1CurrentWide.Proof.CanonicalFinish
      (AspisR1CurrentWide.Proof.recordWideToFinish
        (AspisR1S9OwnedFromLimbsMapV1.wideToParser
          (AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned out))) := by
  have hmap := congrArg
    (AspisR1S9ActualWeightsFieldOwnedMapV1.mapResult
      AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned) h
  rw [AspisR1S9ActualWeightsFieldOwnedMapV1.actual_weights_field_maps_to_owned] at hmap
  have howned : AspisR1S9FieldOwnedV1.weights.field bytes i =
      .ok (AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned out) := by
    simpa only [AspisR1S9ActualWeightsFieldOwnedMapV1.mapResult,
      AspisR1S9ActualFromLimbsOwnedMapV1.mapResult] using hmap
  exact AspisR1S9OwnedFieldCanonicalV1.selected_field_success_canonical
    bytes i (AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned out) howned

#print axioms actual_field_success_canonical

end AspisR1S9ActualFieldSuccessCanonicalV1
