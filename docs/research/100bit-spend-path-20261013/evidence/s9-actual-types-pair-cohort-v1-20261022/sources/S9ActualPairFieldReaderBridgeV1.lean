import S9ActualWeightsFieldOwnedMapV1
import AspisR1S9PairCallerStepV1.Funs
import S9PairCallerStepOwnedFieldBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualPairFieldReaderBridgeV1

abbrev mapResult {A B : Type} (f : A → B) : Result A → Result B :=
  AspisR1S9ActualWeightsFieldOwnedMapV1.mapResult f

def actualToPairW (x : AspisR1S9ActualFieldTypesOwnedMapV1.ActualWide) :
    AspisR1S9PairCallerStepV1.field.WideExact :=
  AspisR1S9PairCallerStepV1.fromOwnedW
    (AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned x)

private theorem mapResult_comp {A B C : Type} (f : A → B) (g : B → C)
    (m : Result A) :
    mapResult g (mapResult f m) = mapResult (fun x => g (f x)) m := by
  cases m <;> rfl

private theorem mapResult_bind_ok {A B : Type} (f : A → B)
    (m : Result A) :
    mapResult f m = (do let x ← m; .ok (f x)) := by
  cases m <;> rfl

/-- The actual attempt7 reader maps through the owned field implementation and
then the Pair caller's explicit field carrier map, preserving the full Result. -/
theorem actual_weights_field_maps_to_pair (bytes : Slice U8) (i : Usize) :
    mapResult actualToPairW
      (AspisR1S9ActualFieldTypesCutV1.weights.field bytes i) =
    AspisR1S9PairCallerStepV1.weights.field bytes i := by
  calc
    mapResult actualToPairW
        (AspisR1S9ActualFieldTypesCutV1.weights.field bytes i) =
      mapResult AspisR1S9PairCallerStepV1.fromOwnedW
        (mapResult AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned
          (AspisR1S9ActualFieldTypesCutV1.weights.field bytes i)) := by
            symm
            exact mapResult_comp
              AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned
              AspisR1S9PairCallerStepV1.fromOwnedW
              (AspisR1S9ActualFieldTypesCutV1.weights.field bytes i)
    _ = mapResult AspisR1S9PairCallerStepV1.fromOwnedW
        (AspisR1S9FieldOwnedV1.weights.field bytes i) := by
          exact congrArg
            (AspisR1S9ActualWeightsFieldOwnedMapV1.mapResult
              AspisR1S9PairCallerStepV1.fromOwnedW)
            (AspisR1S9ActualWeightsFieldOwnedMapV1.actual_weights_field_maps_to_owned
              bytes i)
    _ = AspisR1S9PairCallerStepV1.weights.field bytes i := by
          unfold AspisR1S9PairCallerStepV1.weights.field
          exact mapResult_bind_ok AspisR1S9PairCallerStepV1.fromOwnedW
            (AspisR1S9FieldOwnedV1.weights.field bytes i)

/-- Canonicality of the actual selected-reader result follows from the same
successful actual call, through its mapped Pair call and the existing Pair
reader provenance theorem. -/
theorem actual_field_success_pair_canonical
    (bytes : Slice U8) (i : Usize)
    (out : AspisR1S9ActualFieldTypesOwnedMapV1.ActualWide)
    (h : AspisR1S9ActualFieldTypesCutV1.weights.field bytes i = .ok out) :
    AspisR1S9CurrentFieldOpsV1.Canonical
      (AspisR1S9PairCallerStepV1.toP6W (actualToPairW out)) := by
  have hm := congrArg (mapResult actualToPairW) h
  rw [actual_weights_field_maps_to_pair] at hm
  have hvalue : mapResult actualToPairW (.ok out) =
      .ok (actualToPairW out) := by rfl
  rw [hvalue] at hm
  have hp : AspisR1S9PairCallerStepV1.weights.field bytes i =
      .ok (actualToPairW out) := hm
  obtain ⟨owned, start, next, finish, selected, arr,
      howned, hout, hstart, hnext, hfinish, hselected, hlen, hslice,
      hlimbs, hparser, hpacked, hcan⟩ :=
    AspisR1S9PairCallerStepOwnedFieldBridgeV1.pair_field_success_actual_reader
      bytes i (actualToPairW out) hp
  exact hcan

#print axioms actual_weights_field_maps_to_pair
#print axioms actual_field_success_pair_canonical

end AspisR1S9ActualPairFieldReaderBridgeV1
