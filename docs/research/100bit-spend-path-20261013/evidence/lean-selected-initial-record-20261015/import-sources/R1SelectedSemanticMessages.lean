import R1SelectedTranscriptParams
import R1SemanticPayloadView

/-! Typed semantic-record payloads embedded in the already bounded selected
message carrier. This is byte-codec and view plumbing only; it does not
establish source acceptance, protocol completion, or a probability claim. -/
set_option autoImplicit false

namespace AspisR1.SelectedSemanticMessages

open AspisR1.SelectedTranscriptParams
open AspisR1.SemanticRecordCodec
open AspisR1.SemanticPayloadView
open R0P R0P.SemSource R0P.Mask

theorem encode_length_le901 {row : Fin 25} (payload : RowPayload row) :
    (SemanticRecordCodec.encode payload).length ≤ 901 := by
  rcases payload with ⟨payload, hvalid⟩
  cases payload with
  | empty =>
      simp [SemanticRecordCodec.encode, SemanticRecordCodec.payloadTag,
        SemanticRecordCodec.payloadBytes, RecordFrameCodec.frame_length]
  | c2Root root =>
      simp [SemanticRecordCodec.encode, SemanticRecordCodec.payloadTag,
        SemanticRecordCodec.payloadBytes, RecordFrameCodec.frame_length,
        AspisV8R19.SourceDuplexStep.bytes_length]
  | maskSum value =>
      simp [SemanticRecordCodec.encode, SemanticRecordCodec.payloadTag,
        SemanticRecordCodec.payloadBytes, RecordFrameCodec.frame_length,
        SemanticCoefficientCodec.encodeLow_length]
  | polynomial coefficients =>
      simp [SemanticRecordCodec.encode, SemanticRecordCodec.payloadTag,
        SemanticRecordCodec.payloadBytes, RecordFrameCodec.frame_length,
        SemanticCoefficientCodec.encodeCoefficients_length]

def ofTyped {row : Fin 25} (payload : RowPayload row) : Message :=
  ⟨SemanticRecordCodec.encode payload, by
    have hlen := encode_length_le901 payload
    norm_num [SelectedTranscriptParams.D]
    omega⟩

def decode (row : Fin 25) (message : Message) : Option (RowPayload row) :=
  SemanticRecordCodec.decode row message.val

theorem decode_ofTyped {row : Fin 25} (payload : RowPayload row) :
    decode row (ofTyped payload) = some payload := by
  exact SemanticRecordCodec.decode_encode payload

theorem decoded_unique {row : Fin 25} (message : Message)
    (payload : RowPayload row)
    (h : decode row message = some payload) :
    message = ofTyped payload := by
  apply Subtype.ext
  exact (SemanticRecordCodec.encode_of_decode row message.val payload h).symm

noncomputable def toSemantic
    (recoverC2 : State → InitialWord × InitialWord)
    (row : Fin 25) (message : Message) : Option (SemMsgZ AspisWideTower.WideExact) :=
  (decode row message).map fun payload =>
    SemanticPayloadView.toMessage recoverC2 payload.val

theorem toSemantic_ofTyped
    (recoverC2 : State → InitialWord × InitialWord)
    {row : Fin 25} (payload : RowPayload row) :
    toSemantic recoverC2 row (ofTyped payload) =
      some (SemanticPayloadView.toMessage recoverC2 payload.val) := by
  simp [toSemantic, decode_ofTyped]

#print axioms encode_length_le901
#print axioms decode_ofTyped
#print axioms decoded_unique
#print axioms toSemantic_ofTyped

end AspisR1.SelectedSemanticMessages
