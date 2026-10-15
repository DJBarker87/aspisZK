import R1LengthFrameCodec
import R1SelectedFieldSequenceCodec
import R1SelectedTranscriptParams
import R1SemanticRecordCodec
import R1PublicByteCursor

/-! Strict byte-model codecs for selected opening rows 27--32. These prove
model-level framing, canonical element encoding, and bounded-message facts.
They make no Rust refinement, commitment-recovery, or acceptance claim. -/
set_option autoImplicit false

namespace AspisR1.OpeningRecordCodec

open AspisR1.FoldedLeafCodec
open AspisR1.SemanticCoefficientCodec
open AspisR1.SelectedFieldSequenceCodec
open AspisR1.SelectedTranscriptParams
open AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

abbrev Byte := AspisR1.SemanticCoefficientCodec.Byte
abbrev Bytes := List Byte
abbrev LowWide := AspisR1.SemanticCoefficientCodec.LowWide
abbrev Wide := AspisR1.FoldedLeafCodec.Wide
abbrev State := AspisV8R19.SourceDuplexStep.State
def stateBytes (s : State) : Bytes := AspisV8R19.SourceDuplexStep.bytes s

inductive Row where
  | gamma
  | kappa
  | first
  | second
  | final
  | rho
  deriving DecidableEq, Repr

/-- Typed payload contents for the six selected opening rows. -/
def Payload : Row → Type
  | .gamma => Fin 29 → LowWide
  | .kappa => Wide
  | .first => Fin 7 → Wide
  | .second => State × (Fin 7 → Wide)
  | .final => Fin 64 → Wide
  | .rho => Unit

def payloadSize : Row → Nat
  | .gamma => 928
  | .kappa => 32
  | .first => 224
  | .second => 256
  | .final => 2048
  | .rho => 0

def encodePayload : (row : Row) → Payload row → Bytes
  | .gamma, coefficients => SelectedFieldSequenceCodec.encodeLow coefficients
  | .kappa, value => FoldedLeafCodec.encodeWide value
  | .first, coefficients => SelectedFieldSequenceCodec.encodeWide coefficients
  | .second, (root, coefficients) => stateBytes root ++ SelectedFieldSequenceCodec.encodeWide coefficients
  | .final, coefficients => SelectedFieldSequenceCodec.encodeWide coefficients
  | .rho, _ => []

def decodePayload : (row : Row) → Bytes → Option (Payload row)
  | .gamma, payload =>
      SelectedFieldSequenceCodec.decodeLow 29 payload
  | .kappa, payload =>
      FoldedLeafCodec.decodeWide payload
  | .first, payload =>
      SelectedFieldSequenceCodec.decodeWide 7 payload
  | .second, payload =>
      (PublicByteCursor.read 32 SemanticRecordCodec.decodeState payload).bind
        fun pair => (SelectedFieldSequenceCodec.decodeWide 7 pair.2).map
          (fun coefficients => (pair.1, coefficients))
  | .final, payload =>
      SelectedFieldSequenceCodec.decodeWide 64 payload
  | .rho, payload =>
      if payload = [] then some () else none

def encode {row : Row} (payload : Payload row) : Bytes :=
  LengthFrameCodec.frame (encodePayload row payload)

def decode (row : Row) (record : Bytes) : Option (Payload row) :=
  (LengthFrameCodec.parse (payloadSize row) record).bind (decodePayload row)

theorem encodePayload_length (row : Row) (payload : Payload row) :
    (encodePayload row payload).length = payloadSize row := by
  cases row with
  | gamma => exact SelectedFieldSequenceCodec.encodeLow_length payload
  | kappa => exact FoldedLeafCodec.encodeWide_length payload
  | first => exact SelectedFieldSequenceCodec.encodeWide_length payload
  | second =>
      rcases payload with ⟨root, coefficients⟩
      simp [encodePayload, payloadSize, stateBytes, bytes_length,
        SelectedFieldSequenceCodec.encodeWide_length]
  | final => exact SelectedFieldSequenceCodec.encodeWide_length payload
  | rho => rfl

theorem encode_length {row : Row} (payload : Payload row) :
    (encode payload).length = 4 + payloadSize row := by
  simp [encode, LengthFrameCodec.frame_length, encodePayload_length]

theorem encode_length_le {row : Row} (payload : Payload row) :
    (encode payload).length ≤ SelectedTranscriptParams.D := by
  rw [encode_length]
  cases row <;> norm_num [SelectedTranscriptParams.D, payloadSize]

theorem decodePayload_encodePayload (row : Row) (payload : Payload row) :
    decodePayload row (encodePayload row payload) = some payload := by
  cases row with
  | gamma =>
      exact SelectedFieldSequenceCodec.decodeLow_encode payload
  | kappa =>
      exact FoldedLeafCodec.decodeWide_encode payload
  | first =>
      exact SelectedFieldSequenceCodec.decodeWide_encode payload
  | second =>
      rcases payload with ⟨root, coefficients⟩
      have hread : PublicByteCursor.read 32 SemanticRecordCodec.decodeState
          (stateBytes root ++ SelectedFieldSequenceCodec.encodeWide coefficients) =
          some (root, SelectedFieldSequenceCodec.encodeWide coefficients) := by
        apply PublicByteCursor.read_encoded 32 SemanticRecordCodec.decodeState
          stateBytes root (SelectedFieldSequenceCodec.encodeWide coefficients) ?_ ?_
        · intro x
          exact AspisV8R19.SourceDuplexStep.bytes_length x
        · exact SemanticRecordCodec.decodeState_bytes
      simp only [decodePayload, encodePayload, hread, Option.bind_some,
        SelectedFieldSequenceCodec.decodeWide_encode, Option.map_some]
  | final =>
      exact SelectedFieldSequenceCodec.decodeWide_encode payload
  | rho =>
      rfl

theorem decode_encode {row : Row} (payload : Payload row) :
    decode row (encode payload) = some payload := by
  unfold decode encode
  rw [LengthFrameCodec.parse_frame (encodePayload row payload) (payloadSize row)
    (encodePayload_length row payload)]
  exact decodePayload_encodePayload row payload

theorem encodePayload_of_decodePayload (row : Row) (bytes : Bytes)
    (payload : Payload row) (h : decodePayload row bytes = some payload) :
    encodePayload row payload = bytes := by
  cases row with
  | gamma => exact SelectedFieldSequenceCodec.encodeLow_of_decode bytes payload h
  | kappa =>
      change FoldedLeafCodec.encodeWide payload = bytes
      have hd : FoldedLeafCodec.decodeWide bytes = some payload := by
        exact h
      exact FoldedLeafCodec.encodeWide_of_decode bytes payload hd
  | first => exact SelectedFieldSequenceCodec.encodeWide_of_decode bytes payload h
  | second =>
      rcases payload with ⟨root, coefficients⟩
      change (PublicByteCursor.read 32 SemanticRecordCodec.decodeState bytes).bind
          (fun pair => (SelectedFieldSequenceCodec.decodeWide 7 pair.2).map
            (fun coeffs => (pair.1, coeffs))) = some (root, coefficients) at h
      rcases Option.bind_eq_some_iff.mp h with ⟨pair, hread, hcoeffMap⟩
      rcases pair with ⟨root', rest⟩
      cases hd : SelectedFieldSequenceCodec.decodeWide 7 rest with
      | none => simp [hd] at hcoeffMap
      | some coeffs =>
          simp [hd] at hcoeffMap
          rcases hcoeffMap with ⟨hroot, hcoeff⟩
          subst root'
          subst coeffs
          have hstate := PublicByteCursor.read_sound 32 SemanticRecordCodec.decodeState
            (fun x : State => stateBytes x) bytes root rest
            (fun bs x hx => SemanticRecordCodec.encode_decodeState bs x hx) hread
          have hvalues := SelectedFieldSequenceCodec.encodeWide_of_decode rest coefficients hd
          calc
            encodePayload .second (root, coefficients) =
                stateBytes root ++ SelectedFieldSequenceCodec.encodeWide coefficients := rfl
            _ = stateBytes root ++ rest := by rw [hvalues]
            _ = bytes := hstate.symm
  | final => exact SelectedFieldSequenceCodec.encodeWide_of_decode bytes payload h
  | rho =>
      cases payload
      simp [decodePayload] at h
      subst bytes
      rfl

theorem encode_of_decode {row : Row} (record : Bytes) (payload : Payload row)
    (h : decode row record = some payload) : encode payload = record := by
  rcases Option.bind_eq_some_iff.mp h with ⟨raw, hframe, hpayload⟩
  have hf := LengthFrameCodec.parse_sound (payloadSize row) record raw hframe
  have hp := encodePayload_of_decodePayload row raw payload hpayload
  unfold encode
  rw [hp]
  exact hf.2.symm

def message {row : Row} (payload : Payload row) : SelectedTranscriptParams.Message :=
  ⟨encode payload, by simpa [SelectedTranscriptParams.D] using encode_length_le payload⟩

theorem decoded_message_unique {row : Row} (m : SelectedTranscriptParams.Message)
    (payload : Payload row) (h : decode row m.val = some payload) :
    m = message payload := by
  apply Subtype.ext
  exact (encode_of_decode m.val payload h).symm

#print axioms encodePayload_length
#print axioms encode_length
#print axioms encode_length_le
#print axioms decodePayload_encodePayload
#print axioms decode_encode
#print axioms encodePayload_of_decodePayload
#print axioms encode_of_decode
#print axioms decoded_message_unique

end AspisR1.OpeningRecordCodec
