import S9ActualFromBytesOwnedMapV1
import AspisR1S9FieldOwnedV1.Funs

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9ActualFieldTypesCutV1

def weights.field
  (bytes : Slice Std.U8) (i : Std.Usize) :
  Result field.wide_exact.WideExact
  := do
  let i1 ← lift (Std.Usize.wrapping_mul i 32#usize)
  let i2 ← lift (Std.Usize.wrapping_add i 1#usize)
  let i3 ← lift (Std.Usize.wrapping_mul i2 32#usize)
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) bytes { start := i1, «end» := i3 }
  let o ← field.wide_exact.WideExact.from_le_bytes s
  core.option.Option.unwrap o


end AspisR1S9ActualFieldTypesCutV1

namespace AspisR1S9ActualWeightsFieldOwnedMapV1

abbrev mapResult {A B : Type} (f : A → B) : Result A → Result B :=
  AspisR1S9ActualFromLimbsOwnedMapV1.mapResult f

private theorem mapResult_bind {A B C : Type} (f : A → B)
    (m : Result C) (k : C → Result A) :
    mapResult f (do let x ← m; k x) = (do let x ← m; mapResult f (k x)) := by
  cases m <;> rfl

private theorem mapResult_decode_unwrap {A B : Type} (f : A → B)
    (m : Result (Option A)) :
    mapResult f (do let x ← m; core.option.Option.unwrap x) =
      (do let x ← mapResult (Option.map f) m; core.option.Option.unwrap x) := by
  cases m with
  | ok x => cases x <;> rfl
  | fail e => rfl
  | div => rfl

private theorem actual_decode_unwrap_maps (bytes : Slice U8) :
    mapResult AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned
      (do let o ← AspisR1S9ActualFieldTypesCutV1.field.wide_exact.WideExact.from_le_bytes bytes
          core.option.Option.unwrap o) =
    (do let o ← AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes bytes
        core.option.Option.unwrap o) := by
  rw [mapResult_decode_unwrap]
  have hm := AspisR1S9ActualFromBytesOwnedMapV1.actual_from_le_bytes_maps_to_owned bytes
  change mapResult (Option.map AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned)
    (AspisR1S9ActualFieldTypesCutV1.field.wide_exact.WideExact.from_le_bytes bytes) =
    AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes bytes at hm
  rw [hm]

private theorem actual_decode_unwrap_distributed (bytes : Slice U8) :
    (do let o ← AspisR1S9ActualFieldTypesCutV1.field.wide_exact.WideExact.from_le_bytes bytes
        mapResult AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned
          (core.option.Option.unwrap o)) =
    (do let o ← AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes bytes
        core.option.Option.unwrap o) := by
  have h := actual_decode_unwrap_maps bytes
  rw [mapResult_bind] at h
  exact h

/-- The exact attempt7 selected-field body maps to the owned implementation,
including its three lifted wrapping-offset operations, slice selection,
actual byte decoder, and Option unwrap. -/
theorem actual_weights_field_maps_to_owned (bytes : Slice U8) (i : Usize) :
    mapResult AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned
      (AspisR1S9ActualFieldTypesCutV1.weights.field bytes i) =
    AspisR1S9FieldOwnedV1.weights.field bytes i := by
  simp only [AspisR1S9ActualFieldTypesCutV1.weights.field,
    AspisR1S9FieldOwnedV1.weights.field, mapResult_bind,
    actual_decode_unwrap_distributed]

#print axioms actual_weights_field_maps_to_owned

end AspisR1S9ActualWeightsFieldOwnedMapV1
