import S9OwnedFromLimbsMapV1
import AspisR1S9FieldOwnedV1.Funs
import AspisR1RecordParser.Funs

open Aeneas Aeneas.Std Result

namespace AspisR1S9OwnedFromBytesMapV1

open AspisR1S9OwnedFromLimbsMapV1

private theorem mapResult_bind {A B C : Type} (f : B → C)
    (m : Result A) (k : A → Result B) :
    mapResult f (do let x ← m; k x) = (do let x ← m; mapResult f (k x)) := by
  cases m <;> rfl

/-- The concrete copied byte decoders commute under the established nested
record map. The length check and all 32 ordered byte reads stay in the body;
only the result map is moved through those binds. -/
theorem from_le_bytes_maps (bytes : Slice U8) :
    mapOptionResult wideToParser
      (AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes bytes) =
    AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes := by
  unfold AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes
    AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
  simp only [mapOptionResult, AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.BYTE_LEN,
    AspisR1RecordParser.field.wide_exact.WideExact.BYTE_LEN]
  rw [mapResult_ite]
  split_ifs with hlen
  · simp only [mapResult, Option.map_none]
  · have hm (limbs : Array U32 8#usize) :
        mapResult (Option.map wideToParser)
          (AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_limbs limbs) =
        AspisR1RecordParser.field.wide_exact.WideExact.from_limbs limbs :=
      from_limbs_maps limbs
    simp only [mapResult_bind, hm]

#print axioms from_le_bytes_maps

end AspisR1S9OwnedFromBytesMapV1
