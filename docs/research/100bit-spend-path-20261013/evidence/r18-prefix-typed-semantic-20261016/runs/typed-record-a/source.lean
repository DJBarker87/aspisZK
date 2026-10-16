import R1RecordFrameCodec
import R1SemanticCoefficientCodec
import R1PrefixedStateCodec

/-! Typed byte-model for the five semantic record kinds used by rows 0–24.
This composes exact record framing with the existing strict payload codecs;
it does not establish correspondence with the Rust caller. -/
set_option autoImplicit false

namespace AspisR1.SemanticRecordCodec

open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.SemanticCoefficientCodec

abbrev Byte := SemanticCoefficientCodec.Byte
abbrev Bytes := List Byte

inductive Payload where
  | empty
  | c2Root (root : State)
  | maskSum (value : LowWide)
  | polynomial (coefficients : Coefficients)

def validRow (row : Fin 25) : Payload → Prop
  | .empty => row.val < 2 ∨ (3 ≤ row.val ∧ row.val < 14)
  | .c2Root _ => row.val = 2
  | .maskSum _ => row.val = 14
  | .polynomial _ => 15 ≤ row.val

abbrev RowPayload (row : Fin 25) := { payload : Payload // validRow row payload }

def payloadBytes : Payload → Bytes
  | .empty => []
  | .c2Root root => bytes root
  | .maskSum value => encodeLow value
  | .polynomial coefficients => encodeCoefficients coefficients

def payloadTag : Payload → Byte
  | .empty => 0
  | .c2Root _ => 1
  | .maskSum _ => 3
  | .polynomial _ => 2

def encode {row : Fin 25} (payload : RowPayload row) : Bytes :=
  RecordFrameCodec.frame (payloadTag payload.val) (payloadBytes payload.val)

def decodeState (payload : Bytes) : Option State :=
  if h : payload.length = 32 then some (stateOfBytes payload) else none

def decode (row : Fin 25) (record : Bytes) : Option (RowPayload row) :=
  if h2 : row.val = 2 then
    (RecordFrameCodec.parse 1 32 record).bind fun payload =>
      (decodeState payload).map fun root =>
        ⟨.c2Root root, by simpa [validRow] using h2⟩
  else if h14 : row.val = 14 then
    (RecordFrameCodec.parse 3 32 record).bind fun payload =>
      (decodeLow payload).map fun value =>
        ⟨.maskSum value, by simpa [validRow] using h14⟩
  else if hpoly : 15 ≤ row.val then
    (RecordFrameCodec.parse 2 896 record).bind fun payload =>
      (decodeCoefficients payload).map fun coefficients =>
        ⟨.polynomial coefficients, by simpa [validRow] using hpoly⟩
  else
    (RecordFrameCodec.parse 0 0 record).map fun _ =>
      ⟨.empty, by simp only [validRow]; omega⟩

theorem decodeState_bytes (root : State) : decodeState (bytes root) = some root := by
  have hlen : (bytes root).length = 32 := bytes_length root
  have hs : stateOfBytes (bytes root) = root := by
    simpa using (stateOfBytes_bytes root ([] : Bytes))
  simp [decodeState, hlen, hs]

theorem encode_decodeState (payload : Bytes) (root : State)
    (h : decodeState payload = some root) : bytes root = payload := by
  unfold decodeState at h
  split at h
  · have hs : stateOfBytes payload = root := Option.some.inj h
    calc
      bytes root = bytes (stateOfBytes payload) := by rw [hs]
      _ = payload := by
        have hp : payload.length = 32 := by assumption
        exact (PrefixedStateCodec.bytes_stateOfBytes payload hp)
  · simp at h

theorem decode_encode {row : Fin 25} (payload : RowPayload row) :
    decode row (encode payload) = some payload := by
  rcases payload with ⟨payload, hvalid⟩
  cases payload with
  | empty =>
      have hrow : row.val < 2 ∨ (3 ≤ row.val ∧ row.val < 14) := hvalid
      have hnot2 : row.val ≠ 2 := by omega
      have hnot14 : row.val ≠ 14 := by omega
      have hnotpoly : ¬ 15 ≤ row.val := by omega
      have hp : RecordFrameCodec.parse 0 0 (RecordFrameCodec.frame 0 ([] : Bytes)) = some [] :=
        RecordFrameCodec.parse_frame 0 [] 0 rfl
      change decode row (RecordFrameCodec.frame 0 ([] : Bytes)) =
        some ⟨Payload.empty, hvalid⟩
      unfold decode
      rw [dif_neg hnot2, dif_neg hnot14, dif_neg hnotpoly]
      simp [encode, payloadBytes, payloadTag, hp]
  | c2Root root =>
      have hrow : row.val = 2 := hvalid
      change decode row (RecordFrameCodec.frame 1 (bytes root)) =
        some ⟨Payload.c2Root root, hvalid⟩
      unfold decode
      rw [dif_pos hrow]
      rw [RecordFrameCodec.parse_frame 1 (bytes root) 32 (bytes_length root)]
      simp [encode, payloadBytes, payloadTag, decodeState_bytes]
  | maskSum value =>
      have hrow : row.val = 14 := hvalid
      change decode row (RecordFrameCodec.frame 3 (encodeLow value)) =
        some ⟨Payload.maskSum value, hvalid⟩
      unfold decode
      rw [dif_neg (by omega), dif_pos hrow]
      rw [RecordFrameCodec.parse_frame 3 (encodeLow value) 32 (encodeLow_length value)]
      simp [encode, payloadBytes, payloadTag, decodeLow_encode]
  | polynomial coefficients =>
      have hrow : 15 ≤ row.val := hvalid
      change decode row (RecordFrameCodec.frame 2 (encodeCoefficients coefficients)) =
        some ⟨Payload.polynomial coefficients, hvalid⟩
      unfold decode
      rw [dif_neg (by omega), dif_neg (by omega), dif_pos hrow]
      rw [RecordFrameCodec.parse_frame 2 (encodeCoefficients coefficients) 896
        (encodeCoefficients_length coefficients)]
      simp [encode, payloadBytes, payloadTag, decodeCoefficients_encode]

theorem encode_of_decode (row : Fin 25) (record : Bytes) (payload : RowPayload row)
    (h : decode row record = some payload) : encode payload = record := by
  rcases payload with ⟨payload, hvalid⟩
  cases payload with
  | empty =>
      have hnot2 : row.val ≠ 2 := by simp [validRow] at hvalid; omega
      have hnot14 : row.val ≠ 14 := by simp [validRow] at hvalid; omega
      have hnotpoly : ¬ 15 ≤ row.val := by simp [validRow] at hvalid; omega
      unfold decode at h
      rw [dif_neg hnot2, dif_neg hnot14, dif_neg hnotpoly] at h
      cases hp : RecordFrameCodec.parse 0 0 record with
      | none => simp [hp] at h
      | some raw =>
          have hframe := RecordFrameCodec.parse_sound 0 0 record raw hp
          have hraw : raw = [] := List.eq_nil_of_length_eq_zero hframe.1
          change RecordFrameCodec.frame 0 ([] : Bytes) = record
          simpa [hraw] using hframe.2.symm
  | c2Root root =>
      have hrow : row.val = 2 := hvalid
      unfold decode at h
      rw [dif_pos hrow] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨raw, hp, hm⟩
      have hinner : decodeState raw = some root := by
        simpa using congrArg (Option.map Subtype.val) hm
      have hframe := RecordFrameCodec.parse_sound 1 32 record raw hp
      have hbytes := encode_decodeState raw root hinner
      change RecordFrameCodec.frame 1 (bytes root) = record
      rw [hbytes, hframe.2]
  | maskSum value =>
      have hrow : row.val = 14 := hvalid
      have hnot2 : row.val ≠ 2 := by omega
      unfold decode at h
      rw [dif_neg hnot2, dif_pos hrow] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨raw, hp, hm⟩
      have hinner : decodeLow raw = some value := by
        simpa using congrArg (Option.map Subtype.val) hm
      have hframe := RecordFrameCodec.parse_sound 3 32 record raw hp
      have hbytes := encodeLow_of_decode raw value hinner
      change RecordFrameCodec.frame 3 (encodeLow value) = record
      rw [hbytes, hframe.2]
  | polynomial coefficients =>
      have hrow : 15 ≤ row.val := hvalid
      have hnot2 : row.val ≠ 2 := by omega
      have hnot14 : row.val ≠ 14 := by omega
      unfold decode at h
      rw [dif_neg hnot2, dif_neg hnot14, dif_pos hrow] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨raw, hp, hm⟩
      have hinner : decodeCoefficients raw = some coefficients := by
        simpa using congrArg (Option.map Subtype.val) hm
      have hframe := RecordFrameCodec.parse_sound 2 896 record raw hp
      have hbytes := encodeCoefficients_of_decode raw coefficients hinner
      change RecordFrameCodec.frame 2 (encodeCoefficients coefficients) = record
      rw [hbytes, hframe.2]

theorem polynomial_degree (coefficients : Coefficients) :
    (polynomial coefficients).natDegree ≤ 27 := polynomial_natDegree_le coefficients

#print axioms decodeState_bytes
#print axioms encode_decodeState
#print axioms decode_encode
#print axioms encode_of_decode
#print axioms polynomial_degree

end AspisR1.SemanticRecordCodec
