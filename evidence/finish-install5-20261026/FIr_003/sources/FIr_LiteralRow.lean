import FIq_TypedInitial
import PAln_Records
import R1LiteralSemanticParserFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_LiteralRow
open R0P.Mask
open LiteralTranscript LiteralSemanticCodecBridge

/-- A literal row decodes the very payload selected by the source full codec.
The equality concerns the complete framed record, including its row tag. -/
theorem decode_row (values : SemanticPrefixCodec.Full)
    (rs : List (Message × Challenge))
    (frames : SemanticPrefixCodec.encodeFull values=records rs)
    (length : rs.length=25) (i : Fin 25) :
    SemanticRecordCodec.decode i (record (rs[i.val]'(by rw [length];exact i.isLt)).1)=
      some (values i) := by
  have encoded : (SemanticPrefixCodec.encodeFull values)[i.val]?=
      some (SemanticRecordCodec.encode (values i)) := by
    simp only [SemanticPrefixCodec.encodeFull,List.getElem?_map]
    rw [List.getElem?_eq_getElem (by rw [SemanticPrefixCodec.entriesOf_length];exact i.isLt)]
    rw [SemanticPrefixCodec.entriesOf_getElem values i]
    rfl
  have actual : (records rs)[i.val]?=some (record (rs[i.val]'(by rw [length];exact i.isLt)).1) := by
    simp only [records,List.getElem?_map]
    rw [List.getElem?_eq_getElem (by rw [length];exact i.isLt)]
    rfl
  have same := congrArg (fun xs : List SemanticRecordCodec.Bytes => xs[i.val]?) frames
  rw [encoded,actual] at same
  rw [← Option.some.inj same]
  exact SemanticRecordCodec.decode_encode (values i)

/-- At every literal index, parsing and the source codec choose the same
payload. The message-local callback is retained exactly. -/
theorem parsed_row
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* LiteralSemanticPrefix.E)
    (values : SemanticPrefixCodec.Full) (rs : List (Message × Challenge))
    (out : List (SemMsgZ LiteralSemanticPrefix.E × LiteralSemanticPrefix.E))
    (read : LiteralSemanticPrefix.read eK 0 rs=some out)
    (frames : SemanticPrefixCodec.encodeFull values=records rs)
    (length : rs.length=25) (i : Fin 25) :
    ∃ c, out[i.val]'(by rw [LiteralSemanticPrefix.read_length eK 0 rs out read,length];exact i.isLt)=
      (SemanticPayloadView.toMessage
        (callback eK (rs[i.val]'(by rw [length];exact i.isLt)).1) (values i).val,c) := by
  obtain ⟨bound,parsed,c,parse,challenge,slot⟩ :=
    LiteralSemanticIndex.read_index eK 0 rs out read i.val (by rw [length];exact i.isLt)
  have parse' : LiteralSemanticPrefix.parseMessage eK i
      (rs[i.val]'(by rw [length];exact i.isLt)).1=some parsed := by simpa only [Nat.zero_add] using parse
  rw [parseMessage_eq_decode] at parse'
  split at parse'
  · rw [decode_row values rs frames length i] at parse'
    simp only [Option.map_some,Option.some.injEq] at parse'
    exact ⟨c,by simpa only [Nat.zero_add,← parse'] using slot⟩
  · cases parse'

#print axioms decode_row
#print axioms parsed_row
end AspisR1.FIr_LiteralRow
end
