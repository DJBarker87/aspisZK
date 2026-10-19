import RecordPayloadPartition
import ExtractedRecordValidator

/-! One-record payload consequence of the actual extracted parser.
This does not give Prefix provenance, transcript-state or Rust refinement. -/
set_option autoImplicit false
namespace AspisR1.ExtractedRecordPayloadSoundness
open Aeneas Aeneas.Std Result

/-- For field-bearing rows, successful parsing covers every payload byte by
complete chunks with canonical LE4 words and zero high field component. -/
theorem parse_record_full_payload (row : U8) (record payload : Slice U8)
    (hr : 14 ≤ row.val)
    (h : AspisR1RecordParser.r1_wire.parse_record row record =
      ok (core.result.Result.Ok payload)) :
    (List.toChunksExact 32 (by decide) payload.val).2 = [] ∧
      (List.toChunksExact 32 (by decide) payload.val).1.flatten = payload.val ∧
      ∀ raw ∈ (List.toChunksExact 32 (by decide) payload.val).1,
        ExtractedRecordValidator.CanonicalChunk raw := by
  have hcover := RecordPayloadPartition.successful_payload_covered row record payload h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hvalid⟩ :=
    ExtractedRecordFraming.parse_record_success row record payload h
  exact ⟨hcover.1, hcover.2,
    ExtractedRecordValidator.validate_record_fields_success row payload (hvalid hr)⟩

#print axioms parse_record_full_payload
end AspisR1.ExtractedRecordPayloadSoundness
