import ExtractedRecordStrictLow
import StrictLowChunkCodec
import ExtractedPrefixParserAgreement
import ExtractedRecordPayloadSoundness
import ExtractedPrefixParse

/-! Complete field-bearing payloads of actual successful Prefix records,
represented by the unchanged strict limb codec. No semantic field map,
completed-message identity, or challenge provenance is assumed. -/
namespace AspisR1.ExtractedPrefixStrictPayload
open Aeneas Aeneas.Std Result
open ExtractedRecordByteValue ExtractedRecordStrictCodec ExtractedRecordStrictLow
open RetainedFieldByteCodec StrictWideByteCodec

theorem strict_of_canonical (raw : List U8)
    (h : ExtractedRecordValidator.CanonicalChunk raw) : StrictLowChunk raw := by
  obtain ⟨arr, hb, hc, hz⟩ := h
  have hhigh := canonical_high_zero arr hc hz
  have hlimbs : canonicalLimbs arr hc =
      ((canonicalLimbs arr hc).1, fun _ => zeroLimb) := Prod.ext rfl hhigh
  have hd := strict_decode arr hc
  rw [hlimbs] at hd
  have hbytes : List.ofFn (arrayBytes arr) = raw.map rawByte := by
    rw [arrayBytes_list, hb]
  refine ⟨arrayBytes arr, hbytes, (canonicalLimbs arr hc).1, hd, ?_⟩
  rw [encodeWideLE_of_decodeWideLE _ _ hd]
  exact hbytes

/-- Every payload byte belongs to a strict canonical low chunk. The empty
remainder follows from the actual row table; it is not a validator premise. -/
theorem parse_record_strict_payload (row : U8) (frame payload : Slice U8)
    (hr : 14 ≤ row.val)
    (h : AspisR1PrefixAggregateParser.r1_wire.parse_record row frame =
      ok (core.result.Result.Ok payload)) :
    (List.toChunksExact 32 (by decide) payload.val).2 = [] ∧
      (List.toChunksExact 32 (by decide) payload.val).1.flatten = payload.val ∧
      ∀ raw ∈ (List.toChunksExact 32 (by decide) payload.val).1,
        StrictLowChunk raw := by
  have hold := ExtractedPrefixParserAgreement.parse_record_success row frame payload h
  obtain ⟨hrem, hcover, hc⟩ :=
    ExtractedRecordPayloadSoundness.parse_record_full_payload row frame payload hr hold
  exact ⟨hrem, hcover, fun raw hm => strict_of_canonical raw (hc raw hm)⟩

/-- The parser premise above is supplied by the actual full Prefix result for
any returned row/frame pair, rather than assumed for an arbitrary record. -/
theorem prefix_record_strict_payload (bytes : Slice U8)
    (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix)
    (h : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes =
      ok (core.result.Result.Ok parsed))
    (row : U8) (frame : Slice U8) (hr : 14 ≤ row.val)
    (hm : (row, frame) ∈ ExtractedPrefixTrace.rowOrder.zip parsed.records.val) :
    ∃ payload : Slice U8,
      AspisR1PrefixAggregateParser.r1_wire.parse_record row frame =
        ok (core.result.Result.Ok payload) ∧
      (List.toChunksExact 32 (by decide) payload.val).2 = [] ∧
      (List.toChunksExact 32 (by decide) payload.val).1.flatten = payload.val ∧
      ∀ raw ∈ (List.toChunksExact 32 (by decide) payload.val).1,
        StrictLowChunk raw := by
  obtain ⟨payload, hp⟩ := ExtractedPrefixParse.parse_record_of_success bytes parsed h row frame hm
  exact ⟨payload, hp, parse_record_strict_payload row frame payload hr hp⟩

end AspisR1.ExtractedPrefixStrictPayload

#print axioms AspisR1.ExtractedPrefixStrictPayload.strict_of_canonical
#print axioms AspisR1.ExtractedPrefixStrictPayload.parse_record_strict_payload
#print axioms AspisR1.ExtractedPrefixStrictPayload.prefix_record_strict_payload
