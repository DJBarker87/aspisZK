import S9OwnedFromBytesMapV1
import AspisR1S9FieldOwnedV1.Funs
import AspisR1RecordParser.Funs
import ExtractedRecordByteCanonicality

open Aeneas Aeneas.Std Result

namespace AspisR1S9OwnedFieldReaderReadbackV1

open AspisR1S9OwnedFromLimbsMapV1
open AspisR1S9OwnedFromBytesMapV1

private theorem bind_success {A B : Type} (m : Result A)
    (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = .ok v) : ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Invert the exact copied `weights.field` body while retaining all three
wrapping-arithmetic calls and the actual range-index-selected slice. -/
theorem selected_field_success_readback
    (bytes : Slice U8) (i : Usize) (out : AspisR1S9OwnedFromLimbsMapV1.C)
    (h : AspisR1S9FieldOwnedV1.weights.field bytes i = .ok out) :
    ∃ (start next finish : Usize) (selected : Slice U8),
      lift (Usize.wrapping_mul i 32#usize) = .ok start ∧
      lift (Usize.wrapping_add i 1#usize) = .ok next ∧
      lift (Usize.wrapping_mul next 32#usize) = .ok finish ∧
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
        { start := start, «end» := finish } = .ok selected ∧
      AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes selected =
        .ok (some out) := by
  unfold AspisR1S9FieldOwnedV1.weights.field at h
  obtain ⟨start, hstart, h⟩ := bind_success _ _ _ h
  obtain ⟨next, hnext, h⟩ := bind_success _ _ _ h
  obtain ⟨finish, hfinish, h⟩ := bind_success _ _ _ h
  obtain ⟨selected, hselected, h⟩ := bind_success _ _ _ h
  obtain ⟨decoded, hdecoded, h⟩ := bind_success _ _ _ h
  cases decoded with
  | none => simp only [core.option.Option.unwrap] at h; cases h
  | some value =>
      have hv : value = out := by
        exact Result.ok.inj (show Result.ok value = Result.ok out from by
          simpa only [core.option.Option.unwrap, Result.ofOption] using h)
      subst value
      exact ⟨start, next, finish, selected, hstart, hnext, hfinish,
        hselected, hdecoded⟩

/-- A successful exact owned reader body yields the parser decoder success on
the same source-selected slice. -/
theorem selected_field_success_parser_bytes
    (bytes : Slice U8) (i : Usize) (out : AspisR1S9OwnedFromLimbsMapV1.C)
    (h : AspisR1S9FieldOwnedV1.weights.field bytes i = .ok out) :
    ∃ (selected : Slice U8),
      AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes selected =
        .ok (some (wideToParser out)) := by
  obtain ⟨start, next, finish, selected, _, _, _, _, hdecode⟩ :=
    selected_field_success_readback bytes i out h
  have hmap := congrArg (mapOptionResult wideToParser) hdecode
  rw [from_le_bytes_maps] at hmap
  exact ⟨selected, hmap⟩

/-- Reuse the accepted byte-canonicality/readback theorem on the exact slice
selected by the successful extracted `weights.field` body. -/
theorem selected_field_success_limb_readback
    (bytes : Slice U8) (i : Usize) (out : AspisR1S9OwnedFromLimbsMapV1.C)
    (h : AspisR1S9FieldOwnedV1.weights.field bytes i = .ok out) :
    ∃ (selected : Slice U8) (arr : Array U8 32#usize),
      selected.val.length = 32 ∧
      Array.to_slice arr = selected ∧
      (∀ k : Fin 8,
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr k).val < 2147483647) ∧
      wideToParser out = AspisR1.ExtractedRecordLimbCanonicality.packed
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 0)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 1)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 2)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 3)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 4)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 5)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 6)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 7) := by
  obtain ⟨selected, hdecode⟩ := selected_field_success_parser_bytes bytes i out h
  obtain ⟨hlen, arr, hslice, hlimbs, hpacked⟩ :=
    AspisR1.ExtractedRecordByteCanonicality.slice_success selected (wideToParser out) hdecode
  exact ⟨selected, arr, hlen, hslice, hlimbs, hpacked⟩

#print axioms selected_field_success_readback
#print axioms selected_field_success_parser_bytes
#print axioms selected_field_success_limb_readback

end AspisR1S9OwnedFieldReaderReadbackV1
