import R1SelectedSemanticMessages

/-! The selected bounded message model's row-zero semantic record is the
canonical empty record required by the generic initial walk. This is a byte
model fact only; it does not identify a source parser or accepted run. -/
set_option autoImplicit false

namespace AspisR1.SelectedInitialRecord

open AspisR1.SelectedSemanticMessages
open AspisR1.SemanticRecordCodec
open AspisR1.SelectedTranscriptParams

theorem row0_message_bytes
    (payload : SemanticRecordCodec.RowPayload ⟨0, by omega⟩) :
    (SelectedSemanticMessages.ofTyped payload).val =
      AspisR1.PublicInitFrame.emptyRecord := by
  rcases payload with ⟨payload, hvalid⟩
  cases payload with
  | empty =>
      change RecordFrameCodec.frame 0 [] = _
      exact RecordFrameCodec.zero_tag_empty
  | c2Root root =>
      simp [SemanticRecordCodec.validRow] at hvalid
  | maskSum value =>
      simp [SemanticRecordCodec.validRow] at hvalid
  | polynomial coefficients =>
      simp [SemanticRecordCodec.validRow] at hvalid

theorem params_message_bound : 5 ≤ SelectedTranscriptParams.params.D := by
  change 5 ≤ SelectedTranscriptParams.D
  norm_num [SelectedTranscriptParams.D]

#print axioms row0_message_bytes
#print axioms params_message_bound

end AspisR1.SelectedInitialRecord
