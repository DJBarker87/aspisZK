import OraclePortSelectedObservationsC6

/-! C2 callbacks are metadata for the classifier/extractor, not observations
of the semantic equation checker. Erase just that callback, retaining every
claim, polynomial and challenge. This is not equality of semantic messages. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortSemanticObservationsC6
open LiteralAcceptanceTerminal R0P.Mask R0P.SemSource
open AspisV8R19.DuplexFrames
attribute [local instance] Classical.propDecidable
attribute [local irreducible] R3SemanticRemainingJoins.terminal

/-- Remove the two whole C2 words from a semantic message. -/
def scalarMessage : SemMsgZ E → SemMsgZ E
  | .base (.h1 _ _) => .base .none
  | m => m

def scalarPairs (xs : List (SemMsgZ E × E)) : List (SemMsgZ E × E) :=
  xs.map fun mc => (scalarMessage mc.1,mc.2)

theorem toMessage_scalar (recover : SemanticPayloadView.State →
    SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (p : SemanticRecordCodec.Payload) :
    scalarMessage (SemanticPayloadView.toMessage recover p) =
      scalarMessage (SemanticPayloadView.toMessage (fun _ => (fun _ => 0,fun _ => 0)) p) := by
  cases p <;> rfl

theorem valid_enrich (w : CanonicalCutEnrichedTranscript.Words) (row : Nat)
    (m : LiteralTranscript.Message) :
    LiteralTranscript.valid row (CanonicalCutEnrichedTranscript.enrichMessage w m) ↔
      LiteralTranscript.valid row m := by
  cases m with
  | initial root word =>
    by_cases h : row = 0 <;> simp [LiteralTranscript.valid,CanonicalCutEnrichedTranscript.enrichMessage,h]
  | payload bytes => rfl
  | c2 bytes word =>
    by_cases h : row = 2 <;> simp [LiteralTranscript.valid,CanonicalCutEnrichedTranscript.enrichMessage,h]
  | second bytes word =>
    by_cases h : row = 30 <;> simp [LiteralTranscript.valid,CanonicalCutEnrichedTranscript.enrichMessage,h]

theorem parse_scalar (w : CanonicalCutEnrichedTranscript.Words)
    (row : Fin 25) (m : LiteralTranscript.Message) :
    (LiteralSemanticPrefix.parseMessage LiteralOpeningView.eK row
      (CanonicalCutEnrichedTranscript.enrichMessage w m)).map scalarMessage =
    (LiteralSemanticPrefix.parseMessage LiteralOpeningView.eK row m).map scalarMessage := by
  rw [LiteralSemanticCodecBridge.parseMessage_eq_decode,
    LiteralSemanticCodecBridge.parseMessage_eq_decode,valid_enrich]
  have record : LiteralSemanticCodecBridge.record
      (CanonicalCutEnrichedTranscript.enrichMessage w m) =
      LiteralSemanticCodecBridge.record m := by cases m <;> rfl
  rw [record]
  by_cases hv : LiteralTranscript.valid row.val m
  · simp only [if_pos hv,Option.map_map]
    apply congrArg (fun f => Option.map f (SemanticRecordCodec.decode row
      (LiteralSemanticCodecBridge.record m)))
    funext p
    exact (toMessage_scalar _ p.val).trans (toMessage_scalar _ p.val).symm
  · simp only [if_neg hv,Option.map_none]

/-- Scalar semantic reading commutes with word enrichment, including failures.
The callback may differ at row two; its scalar observation cannot differ. -/
theorem read_scalar (w : CanonicalCutEnrichedTranscript.Words) (offset : Nat)
    (xs : TranscriptRounds) :
    (LiteralSemanticPrefix.read LiteralOpeningView.eK offset
      (xs.map fun mc => (CanonicalCutEnrichedTranscript.enrichMessage w mc.1,mc.2))).map scalarPairs =
    (LiteralSemanticPrefix.read LiteralOpeningView.eK offset xs).map scalarPairs := by
  induction xs generalizing offset with
  | nil => rfl
  | cons mc rest ih =>
    rcases mc with ⟨m,c⟩
    by_cases h : offset < 25
    · cases cv : c.1 with
      | queries result => simp only [List.map_cons,LiteralSemanticPrefix.read,dif_pos h,cv,Option.map_none]
      | ordinary v =>
        have hp := parse_scalar w ⟨offset,h⟩ m
        have ht := ih (offset+1)
        cases a : LiteralSemanticPrefix.parseMessage LiteralOpeningView.eK ⟨offset,h⟩
          (CanonicalCutEnrichedTranscript.enrichMessage w m) <;>
          cases b : LiteralSemanticPrefix.parseMessage LiteralOpeningView.eK ⟨offset,h⟩ m <;>
          simp only [a,b,Option.map_none,Option.map_some,Option.some.injEq,reduceCtorEq] at hp
        · simp only [List.map_cons,LiteralSemanticPrefix.read,dif_pos h,cv,a,b,Option.bind_none,Option.map_none]
        · rename_i x y
          cases ta : LiteralSemanticPrefix.read LiteralOpeningView.eK (offset+1)
            (rest.map fun mc => (CanonicalCutEnrichedTranscript.enrichMessage w mc.1,mc.2)) <;>
            cases tb : LiteralSemanticPrefix.read LiteralOpeningView.eK (offset+1) rest <;>
            simp only [ta,tb,Option.map_none,Option.map_some,Option.some.injEq,reduceCtorEq] at ht
          · simp only [List.map_cons,LiteralSemanticPrefix.read,dif_pos h,cv,a,b,Option.bind_some,ta,tb,Option.map_none]
          · simp only [scalarPairs] at ht
            simp only [List.map_cons,LiteralSemanticPrefix.read,dif_pos h,cv,a,b,Option.bind_some,ta,tb,Option.map_some,
              scalarPairs,List.map_cons,hp,ht]
    · simp only [List.map_cons,LiteralSemanticPrefix.read,dif_neg h,Option.map_none]

/-- Claim and coefficient projections ignore callbacks on canonical payload
rounds. These are the projections used by R3, not c2OfZ. -/
theorem payload_projections (recover recover' : SemanticPayloadView.State →
    SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (payloads : SemanticPrefixCodec.Full) (challenges : Fin 25 → E) :
    claimOf (SemanticPayloadView.rounds recover payloads challenges) =
      claimOf (SemanticPayloadView.rounds recover' payloads challenges) ∧
    semPolysZ (SemanticPayloadView.rounds recover payloads challenges) =
      semPolysZ (SemanticPayloadView.rounds recover' payloads challenges) ∧
    (SemanticPayloadView.pairs recover payloads challenges).map Prod.snd =
      (SemanticPayloadView.pairs recover' payloads challenges).map Prod.snd := by
  refine ⟨?_,?_,?_⟩
  · rw [SemanticPayloadView.claimOf_rounds,SemanticPayloadView.claimOf_rounds]
  · rw [SemanticPayloadView.semPolysZ_rounds,SemanticPayloadView.semPolysZ_rounds]
  · simp only [SemanticPayloadView.pairs,List.map_ofFn]
    rfl

#print axioms toMessage_scalar
#print axioms valid_enrich
#print axioms parse_scalar
#print axioms read_scalar
#print axioms payload_projections
end AspisR1.OraclePortSemanticObservationsC6
end
