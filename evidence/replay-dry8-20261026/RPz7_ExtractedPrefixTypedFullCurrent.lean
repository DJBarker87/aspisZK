import ExtractedPrefixParseCore
import ExtractedPrefixTypedFull
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.PrefixAdapter
open r1_wire
def completedRecords (pre : Prefix) : List AspisR1.SemanticRecordCodec.Bytes :=
  (pre.records.val.take 25).map (fun frame => frame.val.map AspisR1.ExtractedRecordByteValue.rawByte)

/-- Supplies the strict full25 typed-codec premise from this concrete parser's
actual success. No completed-record equality or chosen decoder witness is a
premise. The outer caller still has to connect its transcript log to these bytes. -/
theorem parse_typedFull (bytes : Slice U8) (pre : Prefix)
    (h : parseAccepted bytes = ok (.Ok pre)) :
    ∃ values : AspisR1.SemanticPrefixCodec.Full,
      AspisR1.SemanticPrefixCodec.decodeFull (completedRecords pre) = some values ∧
      AspisR1.SemanticPrefixCodec.encodeFull values = completedRecords pre ∧
      AspisR1.SemanticPrefixCodec.decodeFrom 0 (completedRecords pre) =
        some (AspisR1.SemanticPrefixCodec.entriesOf values) := by
  simpa only [completedRecords, AspisR1.ExtractedPrefixTypedFull.completedRecords, toOld] using
    AspisR1.ExtractedPrefixTypedFull.parse_decodeFull bytes (toOld pre) (parse_success bytes pre h)


/-- Symbolic payload lengths; no normalization of concrete901-byte records. -/
theorem encoded_record_bound {row : Fin 25}
    (value : AspisR1.SemanticRecordCodec.RowPayload row) :
    (AspisR1.SemanticRecordCodec.encode value).length ≤ 901 := by
  rcases value with ⟨payload, hvalid⟩
  cases payload with
  | empty =>
    simp only [AspisR1.SemanticRecordCodec.encode,
      AspisR1.RecordFrameCodec.frame_length,
      AspisR1.SemanticRecordCodec.payloadBytes, List.length_nil]
    omega
  | c2Root root =>
    simp only [AspisR1.SemanticRecordCodec.encode,
      AspisR1.RecordFrameCodec.frame_length,
      AspisR1.SemanticRecordCodec.payloadBytes, AspisV8R19.SourceDuplexStep.bytes_length]
    omega
  | maskSum value =>
    simp only [AspisR1.SemanticRecordCodec.encode,
      AspisR1.RecordFrameCodec.frame_length,
      AspisR1.SemanticRecordCodec.payloadBytes,
      AspisR1.SemanticCoefficientCodec.encodeLow_length]
    omega
  | polynomial coefficients =>
    simp only [AspisR1.SemanticRecordCodec.encode,
      AspisR1.RecordFrameCodec.frame_length,
      AspisR1.SemanticRecordCodec.payloadBytes,
      AspisR1.SemanticCoefficientCodec.encodeCoefficients_length]
    omega

/-- The bound is derived from this same actual parser's strict typed result. -/
theorem parsed_record_bound (bytes : Slice U8) (pre : Prefix)
    (h : parseAccepted bytes = ok (.Ok pre))
    (record : AspisR1.SemanticRecordCodec.Bytes) (hm : record ∈ completedRecords pre) :
    record.length ≤ 901 := by
  obtain ⟨values, _, he, _⟩ := parse_typedFull bytes pre h
  rw [← he] at hm
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hm
  exact encoded_record_bound entry.2.value

#print axioms parse_typedFull
#print axioms encoded_record_bound
#print axioms parsed_record_bound
end AspisR1PublicPreparation.PrefixAdapter
