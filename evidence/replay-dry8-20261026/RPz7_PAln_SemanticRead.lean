import RPz7_RawSourceLiteralInitialCall
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_SemanticRead
open LiteralTranscript LiteralSemanticCodecBridge
open AspisR1.TranscriptView

inductive Ready : Nat → List (LiteralTranscript.Message × LiteralTranscript.Challenge) → Prop where
  | nil (row : Nat) : Ready row []
  | cons {row : Nat} {m : LiteralTranscript.Message} {c : LiteralTranscript.Challenge} {rest : List (LiteralTranscript.Message × LiteralTranscript.Challenge)}
      (valid : LiteralTranscript.valid row m)
      (ordinary : ∃ value, c.1=Value.ordinary value)
      (tail : Ready (row+1) rest) : Ready row ((m,c)::rest)

theorem read_of_decode (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* LiteralSemanticPrefix.E)
    (row : Nat) (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge)) (ready : Ready row rs)
    (decoded : List SemanticPrefixCodec.Entry)
    (success : SemanticPrefixCodec.decodeFrom row (records rs)=some decoded) :
    ∃ out, LiteralSemanticPrefix.read eK row rs=some out := by
  induction ready generalizing decoded with
  | nil => exact ⟨[],rfl⟩
  | @cons row m c rest valid ordinary tail ih =>
    change TypedPrefixParser.decode SemanticPrefixCodec.decodeOne row
      (record m::records rest)=some decoded at success
    cases first : SemanticPrefixCodec.decodeOne row (record m) with
    | none => simp [TypedPrefixParser.decode,first] at success
    | some value =>
      cases remainder : SemanticPrefixCodec.decodeFrom (row+1) (records rest) with
      | none =>
        change TypedPrefixParser.decode SemanticPrefixCodec.decodeOne (row+1) (records rest)=none at remainder
        simp [TypedPrefixParser.decode,first,remainder] at success
      | some remaining =>
        obtain ⟨out,read⟩ := ih remaining remainder
        have encoded := SemanticPrefixCodec.encode_of_decodeOne row (record m) value first
        have payload := SemanticRecordCodec.decode_encode value.value
        rw [encoded] at payload
        have parsed : LiteralSemanticPrefix.parseMessage eK ⟨row,value.isLt⟩ m=
            some (SemanticPayloadView.toMessage (callback eK m) value.value.val) := by
          rw [parseMessage_eq_decode,if_pos valid,payload]
          rfl
        obtain ⟨challenge,challengeEq⟩ := ordinary
        refine ⟨(SemanticPayloadView.toMessage (callback eK m) value.value.val,challenge)::out,?_⟩
        simp only [LiteralSemanticPrefix.read,dif_pos value.isLt,challengeEq,
          parsed,Option.bind_some,read,Option.map_some]

#print axioms read_of_decode
end AspisR1.PAln_SemanticRead
end
