import ExtractedPrefixParserAgreement
import ExtractedRecordFraming
import ExtractedRecordByteValue

/-! Exact re-encoding of the actual successful parser's five header bytes.
No retained list-parser success or semantic payload premise is assumed. -/
namespace AspisR1.ExtractedPrefixHeaderBytes
open Aeneas Aeneas.Std Result
open ExtractedRecordByteValue RetainedFieldByteCodec

private theorem five_split (xs : List U8) (b0 b1 b2 b3 b4 : U8)
    (h0 : xs[0]? = some b0) (h1 : xs[1]? = some b1)
    (h2 : xs[2]? = some b2) (h3 : xs[3]? = some b3)
    (h4 : xs[4]? = some b4) :
    xs = [b0,b1,b2,b3,b4] ++ xs.drop 5 := by
  rcases xs with _ | ⟨x0, xs⟩
  · simp at h0
  rcases xs with _ | ⟨x1, xs⟩
  · simp at h1
  rcases xs with _ | ⟨x2, xs⟩
  · simp at h2
  rcases xs with _ | ⟨x3, xs⟩
  · simp at h3
  rcases xs with _ | ⟨x4, xs⟩
  · simp at h4
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq] at h0 h1 h2 h3 h4
  subst x0; subst x1; subst x2; subst x3; subst x4
  rfl

theorem header_word_bytes (b0 b1 b2 b3 : U8) :
    List.ofFn (encodeWordLE
      (core.num.U32.from_le_bytes (Array.make 4#usize [b0,b1,b2,b3])).bv.toFin) =
      [rawByte b0,rawByte b1,rawByte b2,rawByte b3] := by
  rw [← decodeWordLE_agreement, encodeWordLE_decodeWordLE]
  rfl

/-- The size word is the actual decoded U32, with its existing fixed bound. -/
theorem parse_record_encoded_frame (row : U8) (frame payload : Slice U8)
    (h : AspisR1PrefixAggregateParser.r1_wire.parse_record row frame =
      ok (core.result.Result.Ok payload)) :
    ∃ (tag : U8) (size : Usize) (word : RawWord),
      ExtractedRowShape.table row = some (tag, size) ∧
      word.val = size.val ∧ payload.val.length = size.val ∧
      frame.val.map rawByte =
        [rawByte tag] ++ List.ofFn (encodeWordLE word) ++ payload.val.map rawByte := by
  have hold := ExtractedPrefixParserAgreement.parse_record_success row frame payload h
  obtain ⟨tag, size, b0, b1, b2, b3, ht, _, h0, h1, h2, h3, h4, hw, hp, hlen, _⟩ :=
    ExtractedRecordFraming.parse_record_success row frame payload hold
  refine ⟨tag, size, (ExtractedRecordFraming.headerValue b0 b1 b2 b3).bv.toFin,
    ht, hw, hlen, ?_⟩
  have hs := five_split frame.val tag b0 b1 b2 b3 h0 h1 h2 h3 h4
  have hb : payload.val = frame.val.drop 5 := by
    rw [hp]
    rfl
  have he := congrArg (List.map rawByte) hs
  simpa only [List.map_append, List.map_cons, List.map_nil,
    ExtractedRecordFraming.headerValue, header_word_bytes, hb,
    List.cons_append, List.nil_append] using he

end AspisR1.ExtractedPrefixHeaderBytes

#print axioms AspisR1.ExtractedPrefixHeaderBytes.header_word_bytes
#print axioms AspisR1.ExtractedPrefixHeaderBytes.parse_record_encoded_frame
