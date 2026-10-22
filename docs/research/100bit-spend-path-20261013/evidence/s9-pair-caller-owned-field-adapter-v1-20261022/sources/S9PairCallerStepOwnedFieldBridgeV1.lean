import AspisR1S9PairCallerStepV1.Funs
import S9OwnedFieldReaderReadbackV1
import S9OwnedFieldCanonicalV1
import S9OwnedFromBytesMapV1
import ExtractedRecordByteCanonicality

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairCallerStepOwnedFieldBridgeV1

open AspisR1S9PairCallerStepV1
open AspisR1S9OwnedFromLimbsMapV1
open AspisR1S9OwnedFromBytesMapV1
open AspisR1S9OwnedFieldReaderReadbackV1

private theorem bind_success {A B : Type} (m : Result A)
    (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = .ok v) : ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem owned_to_current_eq_finish (x : AspisR1S9FieldOwnedV1.field.wide_exact.WideExact) :
    AspisR1S9CurrentFieldOpsV1.toE (toP6W (fromOwnedW x)) =
      AspisR1CurrentWide.Proof.ofFinishE
        (AspisR1CurrentWide.Proof.recordWideToFinish (wideToParser x)) := by
  cases x <;> rfl

/-- Every successful call through the pair caller's new field slot is backed
by the exact owned extracted field body. The theorem retains its arithmetic
and slice witnesses, parser byte readback, limb bounds, canonicality in the
selected P6/current-wide carrier, and the explicit returned-value map. -/
theorem pair_field_success_actual_reader
    (bytes : Slice Std.U8) (i : Std.Usize) (out : field.WideExact)
    (h : weights.field bytes i = .ok out) :
    ∃ (owned : AspisR1S9FieldOwnedV1.field.wide_exact.WideExact)
      (start next finish : Usize) (selected : Slice U8)
      (arr : Array U8 32#usize),
      AspisR1S9FieldOwnedV1.weights.field bytes i = .ok owned ∧
      out = fromOwnedW owned ∧
      lift (Usize.wrapping_mul i 32#usize) = .ok start ∧
      lift (Usize.wrapping_add i 1#usize) = .ok next ∧
      lift (Usize.wrapping_mul next 32#usize) = .ok finish ∧
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
        { start := start, «end» := finish } = .ok selected ∧
      selected.val.length = 32 ∧
      Array.to_slice arr = selected ∧
      (∀ k : Fin 8,
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr k).val < 2147483647) ∧
      AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes selected =
        .ok (some (wideToParser owned)) ∧
      wideToParser owned = AspisR1.ExtractedRecordLimbCanonicality.packed
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 0)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 1)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 2)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 3)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 4)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 5)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 6)
        (AspisR1.ExtractedRecordByteCanonicality.wordLE arr 7) ∧
      AspisR1S9CurrentFieldOpsV1.Canonical (toP6W out) := by
  unfold weights.field at h
  obtain ⟨owned, howned, hmap⟩ := bind_success _ _ _ h
  have hout : out = fromOwnedW owned := (Result.ok.inj hmap).symm
  obtain ⟨start, next, finish, selected, hstart, hnext, hfinish, hselected, hdecode⟩ :=
    selected_field_success_readback bytes i owned howned
  have hparserMap := congrArg (mapOptionResult wideToParser) hdecode
  rw [from_le_bytes_maps] at hparserMap
  have hparser : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes selected =
      .ok (some (wideToParser owned)) := hparserMap
  obtain ⟨hlen, arr, hslice, hlimbs, hpacked⟩ :=
    AspisR1.ExtractedRecordByteCanonicality.slice_success selected
      (wideToParser owned) hparser
  have hcan := AspisR1S9OwnedFieldCanonicalV1.selected_field_success_canonical
    bytes i owned howned
  have hcarrier : AspisR1S9CurrentFieldOpsV1.toE (toP6W out) =
      AspisR1CurrentWide.Proof.ofFinishE
        (AspisR1CurrentWide.Proof.recordWideToFinish (wideToParser owned)) := by
    rw [hout]
    exact owned_to_current_eq_finish owned
  have hcanP6 : AspisR1S9CurrentFieldOpsV1.Canonical (toP6W out) := by
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE (toP6W out))
    rw [hcarrier]
    exact hcan
  exact ⟨owned, start, next, finish, selected, arr, howned, hout,
    hstart, hnext, hfinish, hselected, hlen, hslice, hlimbs, hparser, hpacked,
    hcanP6⟩

#print axioms pair_field_success_actual_reader

end AspisR1S9PairCallerStepOwnedFieldBridgeV1
