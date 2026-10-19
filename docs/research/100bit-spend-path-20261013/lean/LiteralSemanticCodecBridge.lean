import R1LiteralSemanticPrefix
import R1LiteralSemanticMessageFacts
import R1SemanticPrefixCodec

/-! PROPOSED, not locally compiled. Connect the literal semantic reader to the
accepted completed-record codec. Row zero contributes the fixed empty record;
its literal message still carries C1. This is a relation between Lean models,
not extraction or refinement of Rust Prefix::parse / SemanticTranscript. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralSemanticCodecBridge
attribute [local instance] Classical.propDecidable

open R0P.Mask
open AspisR1.SemanticRecordCodec
open AspisR1.LiteralTranscript

abbrev E := LiteralSemanticPrefix.E
abbrev State := SemanticPayloadView.State
abbrev Bytes := SemanticRecordCodec.Bytes
abbrev Message := LiteralTranscript.Message
abbrev Challenge := LiteralTranscript.Challenge

/-- Total projection of completed record bytes. Constructor validity remains
a separate premise; projecting a second-fold message does not validate it. -/
def record : Message → Bytes
  | .initial _ _ => PublicInitFrame.emptyRecord
  | .payload bs => bs.val
  | .c2 bs _ => bs.val
  | .second bs _ => bs.val

def records (xs : List (Message × Challenge)) : List Bytes :=
  xs.map (fun mc => record mc.1)

def callback (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E) :
    Message → State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord
  | .c2 _ word => fun _ => LiteralSemanticPrefix.c2Pair eK word
  | _ => fun _ => (fun _ => 0, fun _ => 0)

def emptyAtZero : RowPayload (0 : Fin 25) :=
  ⟨.empty, by simp [validRow]⟩

theorem encode_emptyAtZero : encode emptyAtZero = PublicInitFrame.emptyRecord := by
  rfl

theorem decode_emptyAtZero :
    SemanticRecordCodec.decode 0 PublicInitFrame.emptyRecord = some emptyAtZero := by
  rw [← encode_emptyAtZero]
  exact SemanticRecordCodec.decode_encode emptyAtZero

theorem row_zero_payload (payload : RowPayload (0 : Fin 25)) :
    payload = emptyAtZero := by
  apply Subtype.ext
  rcases payload with ⟨payload, hp⟩
  cases payload with
  | empty => rfl
  | c2Root root => simp [validRow] at hp
  | maskSum value => simp [validRow] at hp
  | polynomial coefficients => simp [validRow] at hp

/-- The exact back law required to replace the stored source row-zero record
by the fixed record synthesized at literal/Unified initialization. -/
theorem row_zero_record_of_decode (raw : Bytes) (payload : RowPayload (0 : Fin 25))
    (h : SemanticRecordCodec.decode 0 raw = some payload) :
    raw = PublicInitFrame.emptyRecord := by
  calc
    raw = SemanticRecordCodec.encode payload := (SemanticRecordCodec.encode_of_decode _ _ _ h).symm
    _ = PublicInitFrame.emptyRecord := by rw [row_zero_payload, encode_emptyAtZero]

theorem valid_initial_row (row : Nat) (root : State) (word : LiteralTranscript.C1Word)
    (h : LiteralTranscript.valid row (.initial root word)) : row = 0 := by
  cases row with
  | zero => rfl
  | succ n => simp [LiteralTranscript.valid] at h

/-- The existing literal parser is the strict record decoder followed by its
message-local C2 callback, including the fixed row-zero record. -/
theorem parseMessage_eq_decode
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (row : Fin 25) (m : Message) :
    LiteralSemanticPrefix.parseMessage eK row m =
      if LiteralTranscript.valid row.val m then
        (SemanticRecordCodec.decode row (record m)).map
          (fun p => SemanticPayloadView.toMessage (callback eK m) p.val)
      else none := by
  cases m with
  | initial root word =>
      by_cases hv : LiteralTranscript.valid row.val (.initial root word)
      · have hr : row = 0 := Fin.ext (valid_initial_row row.val root word hv)
        subst row
        simp [LiteralSemanticPrefix.parseMessage, LiteralTranscript.valid,
          record, decode_emptyAtZero, emptyAtZero, SemanticPayloadView.toMessage]
      · simp [LiteralSemanticPrefix.parseMessage, hv]
  | payload bs => rfl
  | c2 bs word => rfl
  | second bs word =>
      have hv : ¬ LiteralTranscript.valid row.val (.second bs word) := by
        have hr := row.isLt
        intro hvalid
        unfold LiteralTranscript.valid at hvalid
        split at hvalid <;> simp_all <;> omega
      simp [LiteralSemanticPrefix.parseMessage, hv]

theorem decode_of_parseMessage
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (row : Fin 25) (m : Message) (parsed : SemMsgZ E)
    (h : LiteralSemanticPrefix.parseMessage eK row m = some parsed) :
    ∃ payload : RowPayload row,
      SemanticRecordCodec.decode row (record m) = some payload := by
  rw [parseMessage_eq_decode] at h
  split at h
  · cases hd : SemanticRecordCodec.decode row (record m) with
    | none => simp [hd] at h
    | some payload => exact ⟨payload, by simp [hd]⟩
  · simp at h

/-- A successful literal read supplies the concrete typed record decode;
ordinary challenges and constructor checks are inherited from that read. -/
theorem decodeFrom_of_read
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (offset : Nat) (xs : List (Message × Challenge))
    (parsed : List (SemMsgZ E × E))
    (h : LiteralSemanticPrefix.read eK offset xs = some parsed) :
    ∃ out, SemanticPrefixCodec.decodeFrom offset (records xs) = some out := by
  induction xs generalizing offset parsed with
  | nil => exact ⟨[], rfl⟩
  | cons item rest ih =>
      rcases item with ⟨message, challenge⟩
      by_cases hoff : offset < 25
      · cases hvalue : challenge.1 with
        | queries result => simp [LiteralSemanticPrefix.read, hoff, hvalue] at h
        | ordinary c =>
            cases hmessage : LiteralSemanticPrefix.parseMessage eK ⟨offset, hoff⟩ message with
            | none => simp [LiteralSemanticPrefix.read, hoff, hvalue, hmessage] at h
            | some current =>
                cases htail : LiteralSemanticPrefix.read eK (offset + 1) rest with
                | none => simp [LiteralSemanticPrefix.read, hoff, hvalue, hmessage, htail] at h
                | some tail =>
                    obtain ⟨payload, hpayload⟩ :=
                      decode_of_parseMessage eK ⟨offset, hoff⟩ message current hmessage
                    obtain ⟨decoded, hdecoded⟩ := ih (offset + 1) tail htail
                    let first : SemanticPrefixCodec.At offset := ⟨hoff, payload⟩
                    have hfirst : SemanticPrefixCodec.decodeOne offset (record message) =
                        some first := by
                      simp [SemanticPrefixCodec.decodeOne, hoff, hpayload, first]
                    refine ⟨⟨offset, first⟩ :: decoded, ?_⟩
                    unfold SemanticPrefixCodec.decodeFrom records at hdecoded
                    simp [SemanticPrefixCodec.decodeFrom, records,
                      TypedPrefixParser.decode, hfirst, hdecoded]
      · simp [LiteralSemanticPrefix.read, hoff] at h

theorem full_of_read
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (xs : List (Message × Challenge)) (parsed : List (SemMsgZ E × E))
    (hlen : xs.length = 25)
    (h : LiteralSemanticPrefix.read eK 0 xs = some parsed) :
    ∃ payloads : SemanticPrefixCodec.Full,
      SemanticPrefixCodec.decodeFull (records xs) = some payloads ∧
      SemanticPrefixCodec.encodeFull payloads = records xs := by
  obtain ⟨out, hout⟩ := decodeFrom_of_read eK 0 xs parsed h
  have hraw : (records xs).length = 25 := by simp [records, hlen]
  let payloads := SemanticPrefixCodec.fullOfDecoded (records xs) out hraw hout
  have hfull : SemanticPrefixCodec.decodeFull (records xs) = some payloads :=
    SemanticPrefixCodec.decodeFull_of_decoded (records xs) out hraw hout
  exact ⟨payloads, hfull, SemanticPrefixCodec.encodeFull_of_decodeFull _ _ hfull⟩

/-- Successful extensions preserve the whole parsed pair, including the
ordinary challenge value. This is for completed records with the same eK. -/
theorem read_prefix_stable
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (offset : Nat) (xs ys : List (Message × Challenge))
    (out : List (SemMsgZ E × E))
    (h : LiteralSemanticPrefix.read eK offset (xs ++ ys) = some out) :
    LiteralSemanticPrefix.read eK offset xs = some (out.take xs.length) := by
  rw [LiteralSemanticPrefix.read_append] at h
  cases hx : LiteralSemanticPrefix.read eK offset xs with
  | none => simp [hx] at h
  | some pre =>
      cases hy : LiteralSemanticPrefix.read eK (offset + xs.length) ys with
      | none => simp [hx, hy] at h
      | some post =>
          have he : pre ++ post = out := by simpa [hx, hy] using h
          have hl := LiteralSemanticPrefix.read_length eK offset xs pre hx
          rw [← he, ← hl, List.take_left]
          exact hx

#print axioms encode_emptyAtZero
#print axioms decode_emptyAtZero
#print axioms row_zero_record_of_decode
#print axioms parseMessage_eq_decode
#print axioms decodeFrom_of_read
#print axioms full_of_read
#print axioms read_prefix_stable

end AspisR1.LiteralSemanticCodecBridge
end

