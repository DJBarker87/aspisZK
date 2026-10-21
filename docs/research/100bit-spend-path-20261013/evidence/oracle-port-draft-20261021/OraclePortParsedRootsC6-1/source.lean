import OraclePortCandidateWordsC6
import R1LiteralReadAtFacts

/-! Bind the compact parser's three roots to the exact reached message bytes.
The C2 and folded roots come from successful typed record decoders. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortParsedRootsC6
open LiteralAcceptanceTerminal
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4

/-- Successful row-two semantics decodes a root in those exact record bytes. -/
theorem c2_record (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (d : MatchingSupport.Data E)
    (matching : LiteralMatchingData.read (typedRows p q tr) = some d)
    (b : LiteralTranscript.BytesMessage) (c : LiteralTranscript.Challenge)
    (row : tr.rounds[2]? = some (.payload b,c)) :
    ∃ root : State, b.val = SemanticRecordCodec.encode
      (⟨.c2Root root,by rfl⟩ : SemanticRecordCodec.RowPayload (2 : Fin 25)) := by
  obtain ⟨v,_,_,_,_,_,_,_,hopen,_⟩ := LiteralMatchingFacts.read_success_components _ d matching
  obtain ⟨length,_,_,sem,_⟩ := LiteralOpeningPrefixFacts.read_prefix_components _ v hopen
  have typed : (typedRows p q tr)[2]? = some (.c2 b (words p q).c2,c) := by
    rw [typedRows,List.getElem?_mapIdx,row]
    rfl
  have small : 2 < ((typedRows p q tr).take 25).length := by omega
  have get : (((typedRows p q tr).take 25)[2]'small).1 = .c2 b (words p q).c2 := by
    have h := typed
    rw [← List.getElem?_take_of_lt (show 2 < 25 by decide),List.getElem?_eq_getElem small] at h
    exact congrArg Prod.fst (Option.some.inj h)
  obtain ⟨_,parsed,_,hparse,_,_⟩ := LiteralSemanticIndex.read_index LiteralOpeningView.eK 0
    ((typedRows p q tr).take 25) v.semantic sem 2 small
  have hparse' : LiteralSemanticPrefix.parseMessage LiteralOpeningView.eK 2 (.c2 b (words p q).c2) = some parsed := by
    simpa only [Nat.zero_add,get] using hparse
  obtain ⟨payload,decoded⟩ := LiteralSemanticCodecBridge.decode_of_parseMessage
    LiteralOpeningView.eK 2 (.c2 b (words p q).c2) parsed hparse'
  change SemanticRecordCodec.decode 2 b.val = some payload at decoded
  have encoded := SemanticRecordCodec.encode_of_decode 2 b.val payload decoded
  rcases payload with ⟨payload,valid⟩
  cases payload with
  | empty => simp [SemanticRecordCodec.validRow] at valid
  | maskSum value => simp [SemanticRecordCodec.validRow] at valid
  | polynomial coeff => simp [SemanticRecordCodec.validRow] at valid
  | c2Root root => exact ⟨root,encoded.symm⟩

/-- Successful row-thirty decoding identifies the exact root/polynomial frame. -/
theorem folded_record (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (d : MatchingSupport.Data E)
    (matching : LiteralMatchingData.read (typedRows p q tr) = some d)
    (b : LiteralTranscript.BytesMessage) (c : LiteralTranscript.Challenge)
    (row : tr.rounds[30]? = some (.payload b,c)) :
    ∃ payload : OpeningRecordCodec.Payload .second, b.val = OpeningRecordCodec.encode payload := by
  obtain ⟨_,staged,_,_,_,_,_,_,_,hstage,_⟩ := LiteralMatchingFacts.read_success_components _ d matching
  have h30 := LiteralReadAtFacts.readSecond_current _ staged hstage
  have typed : (typedRows p q tr)[30]? = some (.second b (words p q).final,c) := by
    rw [typedRows,List.getElem?_mapIdx,row]
    rfl
  have decoded : OpeningRecordCodec.decode .second b.val = some staged.row30 := by
    simpa only [LiteralOpeningStages.readAt,typed,Option.bind_some,LiteralTranscript.valid,
      if_pos trivial,LiteralTranscript.erase] using h30
  exact ⟨staged.row30,(OpeningRecordCodec.encode_of_decode b.val staged.row30 decoded).symm⟩

#print axioms c2_record
#print axioms folded_record
end AspisR1.OraclePortParsedRootsC6
end
