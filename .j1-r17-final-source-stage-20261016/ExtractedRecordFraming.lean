import AspisR1RecordParser.Funs
import ExtractedRowShape

/-!
Framing consequences of success of the exact header-array parser extraction.
The field validator is not unfolded. No Rust execution, field-canonicality,
or prefix-refinement claim is made here.
-/
namespace AspisR1.ExtractedRecordFraming
open Aeneas Aeneas.Std Result

/-- Both kits contain the same exact row_shape declaration and constants. -/
theorem parser_row_shape_eq (row : U8) :
    AspisR1RecordParser.r1_wire.row_shape row =
      AspisR1RowShape.r1_wire.row_shape row := by
  unfold AspisR1RecordParser.r1_wire.row_shape AspisR1RowShape.r1_wire.row_shape
    AspisR1RecordParser.r1_wire.CLAIMS AspisR1RowShape.r1_wire.CLAIMS
    AspisR1RecordParser.r1_wire.POINTS AspisR1RowShape.r1_wire.POINTS
    AspisR1RecordParser.r1_wire.LANES AspisR1RowShape.r1_wire.LANES
  rfl

theorem parser_row_shape_table (row : U8) :
    AspisR1RecordParser.r1_wire.row_shape row =
      ok (ExtractedRowShape.table row) := by
  rw [parser_row_shape_eq, ExtractedRowShape.row_shape_eq_table]

private theorem bind_ok_iff {α β : Type} (m : Result α)
    (f : α → Result β) (y : β) :
    (m >>= f) = ok y ↔ ∃ x, m = ok x ∧ f x = ok y := by
  cases m <;> simp

private theorem index_ok_iff (record : Slice U8) (i : Usize) (x : U8) :
    Slice.index_usize record i = ok x ↔ record.val[i.val]? = some x := by
  unfold Slice.index_usize
  cases h : record[i]? <;> simp_all

private theorem add_ok_val (a b c : Usize) (h : a + b = ok c) :
    c.val = a.val + b.val := by
  have he := UScalar.add_equiv a b
  rw [h] at he
  exact he.2.1

/-- The same little-endian U32 decoder called by the generated parser. -/
def headerValue (b1 b2 b3 b4 : U8) : U32 :=
  core.num.U32.from_le_bytes (Array.make 4#usize [b1, b2, b3, b4])

/-- Concrete framing facts, including returned-slice equality and validation
success as a consequence, never as an added premise. -/
def SuccessfulFraming (row : U8) (record payload : Slice U8) : Prop :=
  ∃ tag size b1 b2 b3 b4,
    ExtractedRowShape.table row = some (tag, size) ∧
    record.val.length = 5 + size.val ∧
    record.val[0]? = some tag ∧
    record.val[1]? = some b1 ∧ record.val[2]? = some b2 ∧
    record.val[3]? = some b3 ∧ record.val[4]? = some b4 ∧
    (headerValue b1 b2 b3 b4).val = size.val ∧
    payload = record.drop 5#usize ∧
    payload.val.length = size.val ∧
    (14 ≤ row.val → AspisR1RecordParser.r1_wire.validate_record_fields row payload =
      ok (core.result.Result.Ok ()))

/-- Successful execution proves framing and returned bytes without any
assumption about the opaque field validator's behavior. -/
theorem parse_record_success (row : U8) (record payload : Slice U8)
    (h : AspisR1RecordParser.r1_wire.parse_record row record =
      ok (core.result.Result.Ok payload)) :
    SuccessfulFraming row record payload := by
  unfold AspisR1RecordParser.r1_wire.parse_record at h
  rw [parser_row_shape_table] at h
  simp only [bind_tc_ok] at h
  cases ht : ExtractedRowShape.table row with
  | none =>
    simp [ht, AspisR1RecordParser.core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  | some pair =>
    rcases pair with ⟨tag, size⟩
    simp only [ht, AspisR1RecordParser.core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    obtain ⟨framedSize, hadd, h⟩ := (bind_ok_iff _ _ _).mp h
    have hlen : Slice.len record = framedSize := by
      by_contra hn
      simp [hn] at h
    simp [hlen] at h
    have hlength : record.val.length = 5 + size.val := by
      have hv := congrArg UScalar.val hlen
      have ha := add_ok_val _ _ _ hadd
      simpa using hv.trans ha
    obtain ⟨actualTag, h0, h⟩ := (bind_ok_iff _ _ _).mp h
    have htag : actualTag = tag := by
      apply UScalar.eq_of_val_eq
      by_contra hn
      simp [hn] at h
    subst actualTag
    simp only [↓reduceIte] at h
    obtain ⟨b1, h1, h⟩ := (bind_ok_iff _ _ _).mp h
    obtain ⟨b2, h2, h⟩ := (bind_ok_iff _ _ _).mp h
    obtain ⟨b3, h3, h⟩ := (bind_ok_iff _ _ _).mp h
    obtain ⟨b4, h4, h⟩ := (bind_ok_iff _ _ _).mp h
    simp only [lift, bind_tc_ok] at h
    have hdecl :
        (core.num.U32.from_le_bytes (Array.make 4#usize [b1, b2, b3, b4])).val = size.val := by
      by_contra hn
      simp [hn] at h
    simp only [U32.cast_Usize_val_eq, hdecl, ↓reduceIte] at h
    obtain ⟨actualPayload, hs, h⟩ := (bind_ok_iff _ _ _).mp h
    have h5 : 5 ≤ record.val.length := by omega
    have hdrop : actualPayload = record.drop 5#usize := by
      symm
      simpa [core.slice.index.SliceIndexRangeFromUsizeSlice.index, h5] using hs
    have hout : actualPayload = payload ∧
        (14 ≤ row.val → AspisR1RecordParser.r1_wire.validate_record_fields row actualPayload =
          ok (core.result.Result.Ok ())) := by
      by_cases hr : 14 ≤ row.val
      · simp only [if_pos hr] at h
        obtain ⟨validated, hv, h⟩ := (bind_ok_iff _ _ _).mp h
        cases validated with
        | Ok u =>
          cases u
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
            Result.ok.injEq, core.result.Result.Ok.injEq] at h
          exact ⟨h, fun _ => hv⟩
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
      · simp only [if_neg hr, Result.ok.injEq, core.result.Result.Ok.injEq] at h
        refine ⟨h, ?_⟩
        intro hrval
        exact False.elim (hr hrval)
    rcases hout with ⟨heq, hvalid⟩
    have hpayload : payload = record.drop 5#usize := heq.symm.trans hdrop
    have hvalidPayload : 14 ≤ row.val →
        AspisR1RecordParser.r1_wire.validate_record_fields row payload =
          ok (core.result.Result.Ok ()) := by
      simpa only [heq] using hvalid
    refine ⟨tag, size, b1, b2, b3, b4, ht, hlength, ?_, ?_, ?_, ?_, ?_, ?_, hpayload, ?_, hvalidPayload⟩
    · simpa using (index_ok_iff _ _ _).mp h0
    · simpa using (index_ok_iff _ _ _).mp h1
    · simpa using (index_ok_iff _ _ _).mp h2
    · simpa using (index_ok_iff _ _ _).mp h3
    · simpa using (index_ok_iff _ _ _).mp h4
    · simpa only [headerValue] using hdecl
    · rw [hpayload]
      simp [Slice.drop, hlength]

end AspisR1.ExtractedRecordFraming

#print axioms AspisR1.ExtractedRecordFraming.parser_row_shape_eq
#print axioms AspisR1.ExtractedRecordFraming.parser_row_shape_table

#print axioms AspisR1.ExtractedRecordFraming.parse_record_success
