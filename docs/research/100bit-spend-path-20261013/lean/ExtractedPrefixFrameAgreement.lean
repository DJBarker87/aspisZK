import ExtractedPrefixHeaderBytes
import ExtractedPrefixParse
import R1RecordLengthCodec
import R1RecordParserModel

/-! Successful actual parsing supplies the unchanged retained record-frame
and list-parser interfaces, using exact bytes rather than a success premise. -/
namespace AspisR1.ExtractedPrefixFrameAgreement
open Aeneas Aeneas.Std Result
open ExtractedRecordByteValue RetainedFieldByteCodec

theorem parse_record_frame_success (row : U8) (frame payload : Slice U8)
    (h : AspisR1PrefixAggregateParser.r1_wire.parse_record row frame =
      ok (core.result.Result.Ok payload)) :
    ∃ (tag : U8) (size : Usize),
      ExtractedRowShape.table row = some (tag, size) ∧
      payload.val.length = size.val ∧
      RecordFrameCodec.parse (rawByte tag) size.val (frame.val.map rawByte) =
        some (payload.val.map rawByte) ∧
      RecordParserModel.parse (rawByte tag) size.val (frame.val.map rawByte) =
        some (payload.val.map rawByte) := by
  obtain ⟨tag, size, word, ht, hw, hlen, hbytes⟩ :=
    ExtractedPrefixHeaderBytes.parse_record_encoded_frame row frame payload h
  have hsize : size.val < 2 ^ 32 := by
    rw [← hw]
    exact word.isLt
  have hword : (⟨size.val, hsize⟩ : RawWord) = word := Fin.ext hw.symm
  have hlength : PublicInitFrame.lengthBytes size.val = List.ofFn (encodeWordLE word) := by
    rw [RecordLengthCodec.lengthBytes_eq_encodeWordLE size.val hsize, hword]
  have hframe : frame.val.map rawByte =
      RecordFrameCodec.frame (rawByte tag) (payload.val.map rawByte) := by
    unfold RecordFrameCodec.frame RecordFrameCodec.header
    simp only [List.length_map, hlen, hlength]
    exact hbytes
  have hp : RecordFrameCodec.parse (rawByte tag) size.val (frame.val.map rawByte) =
      some (payload.val.map rawByte) := by
    apply (RecordFrameCodec.parse_eq_some_iff _ _ _ _).mpr
    exact ⟨by simpa only [List.length_map] using hlen, hframe⟩
  refine ⟨tag, size, ht, hlen, hp, ?_⟩
  rw [RecordParserModel.parse_eq_recordFrame_parse _ _ _ hsize]
  exact hp

/-- The successful inner parser is supplied by the actual complete Prefix
execution for each returned row/frame pair. -/
theorem prefix_record_frame_success (bytes : Slice U8)
    (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix)
    (h : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes =
      ok (core.result.Result.Ok parsed))
    (row : U8) (frame : Slice U8)
    (hm : (row, frame) ∈ ExtractedPrefixTrace.rowOrder.zip parsed.records.val) :
    ∃ (tag : U8) (size : Usize) (payload : Slice U8),
      ExtractedRowShape.table row = some (tag, size) ∧
      AspisR1PrefixAggregateParser.r1_wire.parse_record row frame =
        ok (core.result.Result.Ok payload) ∧
      payload.val.length = size.val ∧
      RecordFrameCodec.parse (rawByte tag) size.val (frame.val.map rawByte) =
        some (payload.val.map rawByte) ∧
      RecordParserModel.parse (rawByte tag) size.val (frame.val.map rawByte) =
        some (payload.val.map rawByte) := by
  obtain ⟨payload, hp⟩ := ExtractedPrefixParse.parse_record_of_success bytes parsed h row frame hm
  obtain ⟨tag, size, ht, hlen, hf, hm⟩ := parse_record_frame_success row frame payload hp
  exact ⟨tag, size, payload, ht, hp, hlen, hf, hm⟩

end AspisR1.ExtractedPrefixFrameAgreement

#print axioms AspisR1.ExtractedPrefixFrameAgreement.parse_record_frame_success

#print axioms AspisR1.ExtractedPrefixFrameAgreement.prefix_record_frame_success
