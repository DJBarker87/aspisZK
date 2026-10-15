import R1SelectedFieldSequenceCodec
import R1RecordFrameCodec
import R1SelectedTranscriptParams

/-! Strict byte-model records for the two circle rows. The first retains all
116 low-field values, including the 29 extra values after the 87 point
claims. The second retains 29 values. These are codec identities, not a
Rust refinement or a proof of the opening-view algebraic premises. -/
set_option autoImplicit false
namespace AspisR1.CircleRecordCodec

abbrev Byte := SemanticCoefficientCodec.Byte
abbrev LowWide := SemanticCoefficientCodec.LowWide

def count (row : Fin 2) : Nat := if row.val = 0 then 116 else 29
def tag (row : Fin 2) : Byte := ⟨4 + row.val, by omega⟩
abbrev Payload (row : Fin 2) := Fin (count row) → LowWide

def encode {row : Fin 2} (payload : Payload row) : List Byte :=
  RecordFrameCodec.frame (tag row) (SelectedFieldSequenceCodec.encodeLow payload)

def decode (row : Fin 2) (bytes : List Byte) : Option (Payload row) :=
  (RecordFrameCodec.parse (tag row) (count row * 32) bytes).bind
    (SelectedFieldSequenceCodec.decodeLow (count row))

theorem encode_length {row : Fin 2} (payload : Payload row) :
    (encode payload).length = 5 + count row * 32 := by
  rw [encode, RecordFrameCodec.frame_length, SelectedFieldSequenceCodec.encodeLow_length]

theorem encode_length_le {row : Fin 2} (payload : Payload row) :
    (encode payload).length ≤ 3717 := by
  rw [encode_length]
  unfold count
  split <;> norm_num

theorem decode_encode {row : Fin 2} (payload : Payload row) :
    decode row (encode payload) = some payload := by
  unfold decode encode
  rw [RecordFrameCodec.parse_frame _ _ _ (SelectedFieldSequenceCodec.encodeLow_length payload)]
  simp only [Option.bind_some, SelectedFieldSequenceCodec.decodeLow_encode]

theorem encode_of_decode (row : Fin 2) (bytes : List Byte) (payload : Payload row)
    (h : decode row bytes = some payload) : encode payload = bytes := by
  rcases Option.bind_eq_some_iff.mp h with ⟨raw, hframe, hvalues⟩
  have hf := RecordFrameCodec.parse_sound (tag row) (count row * 32) bytes raw hframe
  have hv := SelectedFieldSequenceCodec.encodeLow_of_decode raw payload hvalues
  unfold encode
  rw [hv]
  exact hf.2.symm

def message {row : Fin 2} (payload : Payload row) : SelectedTranscriptParams.Message :=
  ⟨encode payload, by simpa [SelectedTranscriptParams.D] using encode_length_le payload⟩

theorem decoded_message_unique (row : Fin 2) (m : SelectedTranscriptParams.Message)
    (payload : Payload row) (h : decode row m.val = some payload) :
    m = message payload := by
  apply Subtype.ext
  exact (encode_of_decode row m.val payload h).symm

/-- The first three blocks are the point claims, in point-major order. -/
def pointClaims (payload : Payload 0) (point : Fin 3) (lane : Fin 29) : LowWide :=
  payload ⟨29 * point.val + lane.val, by
    have hp := point.isLt
    have hl := lane.isLt
    change 29 * point.val + lane.val < 116
    omega⟩

/-- The fourth block is retained separately; it must not be discarded by a view. -/
def extra (payload : Payload 0) (lane : Fin 29) : LowWide :=
  payload ⟨87 + lane.val, by
    have hl := lane.isLt
    change 87 + lane.val < 116
    omega⟩

def beforeZ1 (payload : Payload 1) (lane : Fin 29) : LowWide := payload lane

theorem first_length (payload : Payload 0) : (encode payload).length = 3717 :=
  encode_length payload

theorem second_length (payload : Payload 1) : (encode payload).length = 933 :=
  encode_length payload

#print axioms encode_length
#print axioms encode_length_le
#print axioms decode_encode
#print axioms encode_of_decode
#print axioms decoded_message_unique
#print axioms first_length
#print axioms second_length
end AspisR1.CircleRecordCodec
