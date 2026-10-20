import BinGrammar
import RawTranscriptFrameBytes
import R1SemanticRecordCodec
import R1CircleRecordCodec
import R1OpeningRecordCodec

/-! Length separation for the existing literal protocol's typed codecs.
The unrestricted SelectedTranscriptParams.Message carrier enforces only an
upper bound; these results apply to typed encodings / successful decoding. -/
set_option autoImplicit false
namespace AspisR1.BinWireRecordLengths
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem semantic_lengths {row : Fin 25} (p : SemanticRecordCodec.RowPayload row) :
    (SemanticRecordCodec.encode p).length = 5 ∨
    (SemanticRecordCodec.encode p).length = 37 ∨
    (SemanticRecordCodec.encode p).length = 901 := by
  rcases p with ⟨p, hp⟩
  cases p <;> simp [SemanticRecordCodec.encode, SemanticRecordCodec.payloadTag,
    SemanticRecordCodec.payloadBytes, RecordFrameCodec.frame_length, bytes_length,
    SemanticCoefficientCodec.encodeLow_length, SemanticCoefficientCodec.encodeCoefficients_length]

theorem semantic_safe {row : Fin 25} (p : SemanticRecordCodec.RowPayload row) :
    (SemanticRecordCodec.encode p).length ≠ 31 ∧
    (SemanticRecordCodec.encode p).length ≠ 65 := by
  have h := semantic_lengths p
  omega

theorem circle_safe {row : Fin 2} (p : CircleRecordCodec.Payload row) :
    (CircleRecordCodec.encode p).length ≠ 31 ∧
    (CircleRecordCodec.encode p).length ≠ 65 := by
  rw [CircleRecordCodec.encode_length]
  unfold CircleRecordCodec.count
  split <;> omega

theorem opening_payload_safe (row : OpeningRecordCodec.Row) (p : OpeningRecordCodec.Payload row) :
    (OpeningRecordCodec.encodePayload row p).length ≠ 27 := by
  rw [OpeningRecordCodec.encodePayload_length]
  cases row <;> decide

theorem opening_frame_safe (row : OpeningRecordCodec.Row) (p : OpeningRecordCodec.Payload row) :
    (OpeningRecordCodec.encode p).length ≠ 31 ∧
    (OpeningRecordCodec.encode p).length ≠ 65 := by
  rw [OpeningRecordCodec.encode_length]
  cases row <;> decide

theorem absorb_ne_node (state : State) (row : Nat) (record : Bytes)
    (h : record.length ≠ 31) (cs : BinMerkle32Path.Children) :
    BinMerkle32Path.nodeInput cs ≠ RawTranscriptFrameBytes.absorb state row record := by
  apply BinGrammar.node_ne_length
  simp only [RawTranscriptFrameBytes.absorb, List.length_append, bytes_length,
    List.length_cons, List.length_nil]
  omega

theorem semantic_absorb_ne_node {row : Fin 25} (p : SemanticRecordCodec.RowPayload row)
    (state : State) (cs : BinMerkle32Path.Children) :
    BinMerkle32Path.nodeInput cs ≠
      RawTranscriptFrameBytes.absorb state row.val (SemanticRecordCodec.encode p) :=
  absorb_ne_node state row.val _ (semantic_safe p).1 cs

theorem circle_absorb_ne_node {row : Fin 2} (p : CircleRecordCodec.Payload row)
    (state : State) (cs : BinMerkle32Path.Children) :
    BinMerkle32Path.nodeInput cs ≠
      RawTranscriptFrameBytes.absorb state (25 + row.val) (CircleRecordCodec.encode p) :=
  absorb_ne_node state _ _ (circle_safe p).1 cs

theorem opening_absorb_ne_node (row : OpeningRecordCodec.Row) (p : OpeningRecordCodec.Payload row)
    (n : Nat) (state : State) (cs : BinMerkle32Path.Children) :
    BinMerkle32Path.nodeInput cs ≠
      RawTranscriptFrameBytes.absorb state n (OpeningRecordCodec.encode p) :=
  absorb_ne_node state n _ (opening_frame_safe row p).1 cs

#print axioms semantic_lengths
#print axioms semantic_safe
#print axioms circle_safe
#print axioms opening_payload_safe
#print axioms opening_frame_safe
#print axioms absorb_ne_node
#print axioms semantic_absorb_ne_node
#print axioms circle_absorb_ne_node
#print axioms opening_absorb_ne_node
end AspisR1.BinWireRecordLengths
