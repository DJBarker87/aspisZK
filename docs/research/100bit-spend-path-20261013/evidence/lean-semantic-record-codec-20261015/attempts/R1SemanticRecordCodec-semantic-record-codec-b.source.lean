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
        ⟨.c2Root root, by simp [validRow, h2]⟩
  else if h14 : row.val = 14 then
    (RecordFrameCodec.parse 3 32 record).bind fun payload =>
      (decodeLow payload).map fun value =>
        ⟨.maskSum value, by simp [validRow, h14]⟩
  else if hpoly : 15 ≤ row.val then
    (RecordFrameCodec.parse 2 896 record).bind fun payload =>
      (decodeCoefficients payload).map fun coefficients =>
        ⟨.polynomial coefficients, by simp [validRow, hpoly]⟩
  else
    (RecordFrameCodec.parse 0 0 record).map fun _ =>
      ⟨.empty, by simp only [validRow]; omega⟩

theorem decodeState_bytes (root : State) : decodeState (bytes root) = some root := by
  have hlen : (bytes root).length = 32 := bytes_length root
  rw [decodeState, if_pos hlen]
  have hs : stateOfBytes (bytes root) = root := by
    simpa using (stateOfBytes_bytes root ([] : Bytes))
  rw [hs]

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
      unfold decode
      rw [if_neg hnot2, if_neg hnot14, if_neg hnotpoly]
      simp [encode, payloadBytes, payloadTag, hp]
  | c2Root root =>
      have hrow : row.val = 2 := hvalid
      unfold decode
      rw [if_pos hrow]
      rw [RecordFrameCodec.parse_frame 1 (bytes root) 32 (bytes_length root)]
      simp [encode, payloadBytes, payloadTag, decodeState_bytes]
  | maskSum value =>
      have hrow : row.val = 14 := hvalid
      unfold decode
      rw [if_neg (by omega), if_pos hrow]
      rw [RecordFrameCodec.parse_frame 3 (encodeLow value) 32 (encodeLow_length value)]
      simp [encode, payloadBytes, payloadTag, decodeLow_encode]
  | polynomial coefficients =>
      have hrow : 15 ≤ row.val := hvalid
      unfold decode
      rw [if_neg (by omega), if_neg (by omega), if_pos hrow]
      rw [RecordFrameCodec.parse_frame 2 (encodeCoefficients coefficients) 896
        (encodeCoefficients_length coefficients)]
      simp [encode, payloadBytes, payloadTag, decodeCoefficients_encode]

theorem encode_of_decode (row : Fin 25) (record : Bytes) (payload : RowPayload row)
    (h : decode row record = some payload) : encode payload = record := by
  rcases payload with ⟨payload, hvalid⟩
  cases payload with
  | empty =>
      simp only [decode] at h
      split at h
      · simp_all [validRow]
      · split at h
        · simp_all [validRow]
        · split at h
          · simp_all [validRow]
          · have hp := Option.some.inj h
            simp [encode, payloadBytes, payloadTag, RecordFrameCodec.parse_sound] at hp ⊢
  | c2Root root =>
      simp only [decode] at h
      split at h
      · simp only [Option.bind_eq_some_iff] at h
        rcases h with ⟨payloadBytes, hp, hd⟩
        have hframe := RecordFrameCodec.parse_sound 1 32 record payloadBytes hp
        have hbytes := encode_decodeState payloadBytes root hd
        rcases hframe with ⟨hsize, hrecord⟩
        simp [encode, payloadBytes, payloadTag, hbytes, hrecord]
      · simp_all [validRow]
  | maskSum value =>
      simp only [decode] at h
      split at h
      · simp_all [validRow]
      · split at h
        · simp only [Option.bind_eq_some_iff] at h
          rcases h with ⟨payloadBytes, hp, hd⟩
          have hframe := RecordFrameCodec.parse_sound 3 32 record payloadBytes hp
          have hbytes := encodeLow_of_decode payloadBytes value hd
          rcases hframe with ⟨hsize, hrecord⟩
          simp [encode, payloadBytes, payloadTag, hbytes, hrecord]
        · simp_all [validRow]
  | polynomial coefficients =>
      simp only [decode] at h
      split at h
      · simp_all [validRow]
      · split at h
        · simp_all [validRow]
        · split at h
          · simp only [Option.bind_eq_some_iff] at h
            rcases h with ⟨payloadBytes, hp, hd⟩
            have hframe := RecordFrameCodec.parse_sound 2 896 record payloadBytes hp
            have hbytes := encodeCoefficients_of_decode payloadBytes coefficients hd
            rcases hframe with ⟨hsize, hrecord⟩
            simp [encode, payloadBytes, payloadTag, hbytes, hrecord]
          · simp_all [validRow]

theorem polynomial_degree (coefficients : Coefficients) :
    (polynomial coefficients).natDegree ≤ 27 := polynomial_natDegree_le coefficients

#print axioms decodeState_bytes
#print axioms encode_decodeState
#print axioms decode_encode
#print axioms encode_of_decode
#print axioms polynomial_degree

end AspisR1.SemanticRecordCodec
