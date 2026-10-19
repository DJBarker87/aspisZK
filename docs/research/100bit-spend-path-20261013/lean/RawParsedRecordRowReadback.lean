import ExtractedPrefixTypedFullCurrent
import R1SemanticPrefixCodec

/-! Reuse the reached-record slot proof in a narrow source/parser module,
without importing the polynomial-chain graph. -/
set_option autoImplicit false
namespace AspisR1PublicPreparation.RawParsedRecordRowReadback
open Aeneas Aeneas.Std Result

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Source-shaped slot readback for the current generated Prefix owner. -/
theorem validated_record_bytes (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (row : U8) (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
    (h : AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre row =
      ok (.Ok record)) :
    record.row = row ∧ pre.records.val[row.val]? = some record.framed := by
  unfold AspisR1PublicPreparation.r1_wire.Prefix.validated_record at h
  obtain ⟨r, hr, h⟩ := bind_success _ _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, bind_tc_ok] at h
    cases h
  | Ok framed =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    have he : record = { row, framed } :=
      (core.result.Result.Ok.inj (Result.ok.inj h)).symm
    rw [he]
    refine ⟨rfl, ?_⟩
    unfold AspisR1PublicPreparation.r1_wire.Prefix.record at hr
    split at hr
    · cases hr
    · rename_i hrow
      simp only [lift, bind_tc_ok] at hr
      obtain ⟨actual, hi, hr⟩ := bind_success _ _ _ hr
      have ha : actual = framed := core.result.Result.Ok.inj (Result.ok.inj hr)
      unfold Array.index_usize at hi
      split at hi
      · cases hi
      · rename_i value hindex
        have hv : value = actual := Result.ok.inj hi
        change pre.records.val[(UScalar.cast .Usize row).val]? = some value at hindex
        simpa only [U8.cast_Usize_val_eq] using hindex.trans (congrArg some (hv.trans ha))


/-- One fixed encoded Full view determines the typed interpretation of every
successfully reached validated record in the semantic prefix. -/
theorem record_decodes_fixed_row
    (pre : r1_wire.Prefix) (values : AspisR1.SemanticPrefixCodec.Full)
    (hfull : AspisR1.SemanticPrefixCodec.encodeFull values =
      PrefixAdapter.completedRecords pre)
    (i : Fin 25) (row : U8) (record : r1_wire.ValidatedRecord)
    (hrow : row.val = i.val)
    (hrecord : r1_wire.Prefix.validated_record pre row = .ok (.Ok record)) :
    AspisR1.SemanticRecordCodec.decode i
      (record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte) = some (values i) := by
  have hslot := validated_record_bytes pre row record hrecord
  have hraw : pre.records.val[i.val]? = some record.framed := by
    simpa only [hrow] using hslot.2
  have hcompleted : (PrefixAdapter.completedRecords pre)[i.val]? =
      some (record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte) := by
    unfold PrefixAdapter.completedRecords
    rw [List.getElem?_map]
    rw [List.getElem?_take_of_lt (l := pre.records.val) (i := i.val) (j := 25) i.isLt]
    simpa using congrArg (Option.map
      (fun frame => frame.val.map AspisR1.ExtractedRecordByteValue.rawByte)) hraw
  have hencoded : (AspisR1.SemanticPrefixCodec.encodeFull values)[i.val]? =
      some (AspisR1.SemanticRecordCodec.encode (values i)) := by
    simp only [AspisR1.SemanticPrefixCodec.encodeFull, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by
      rw [AspisR1.SemanticPrefixCodec.entriesOf_length]
      exact i.isLt)]
    rw [AspisR1.SemanticPrefixCodec.entriesOf_getElem values i]
    rfl
  have hget := congrArg (fun xs : List AspisR1.SemanticRecordCodec.Bytes => xs[i.val]?) hfull
  rw [hencoded, hcompleted] at hget
  have hframe : AspisR1.SemanticRecordCodec.encode (values i) =
      record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte := Option.some.inj hget
  rw [← hframe]
  exact AspisR1.SemanticRecordCodec.decode_encode (values i)

#print axioms validated_record_bytes
#print axioms record_decodes_fixed_row
end AspisR1PublicPreparation.RawParsedRecordRowReadback
