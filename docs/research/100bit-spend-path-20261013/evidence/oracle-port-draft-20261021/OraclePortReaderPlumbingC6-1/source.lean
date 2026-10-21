import OraclePortSemanticObservationsC6

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortReaderPlumbingC6
open LiteralAcceptanceTerminal OraclePortSemanticObservationsC6
attribute [local instance] Classical.propDecidable

def reword (w : CanonicalCutEnrichedTranscript.Words) (rs : TranscriptRounds) : TranscriptRounds :=
  rs.map fun mc => (CanonicalCutEnrichedTranscript.enrichMessage w mc.1,mc.2)

theorem reword_take (w : CanonicalCutEnrichedTranscript.Words) (rs : TranscriptRounds) (n : Nat) :
    (reword w rs).take n = reword w (rs.take n) := by
  exact (List.map_take ..).symm

theorem erased (w : CanonicalCutEnrichedTranscript.Words) (m : LiteralTranscript.Message) :
    LiteralTranscript.erase (CanonicalCutEnrichedTranscript.enrichMessage w m) = LiteralTranscript.erase m := by
  cases m <;> rfl

theorem ordinaryAt (w : CanonicalCutEnrichedTranscript.Words) (rs : TranscriptRounds) (row : Nat) :
    LiteralChallengeRead.ordinaryAt (reword w rs) row = LiteralChallengeRead.ordinaryAt rs row := by
  unfold LiteralChallengeRead.ordinaryAt reword
  rw [List.getElem?_map]
  cases rs[row]? <;> rfl

theorem readAt {T : Type} (w : CanonicalCutEnrichedTranscript.Words) (rs : TranscriptRounds)
    (row : Nat) (decode : AspisV8R19.DuplexFrames.Bytes → Option T) :
    LiteralOpeningStages.readAt (reword w rs) row decode = LiteralOpeningStages.readAt rs row decode := by
  unfold LiteralOpeningStages.readAt reword
  rw [List.getElem?_map]
  cases h : rs[row]? with
  | none => rfl
  | some mc =>
    simp only [Option.map_some,Option.bind_some,valid_enrich,erased]

theorem readSecond (w : CanonicalCutEnrichedTranscript.Words) (rs : TranscriptRounds) :
    LiteralOpeningStages.readSecond (reword w rs) = LiteralOpeningStages.readSecond rs := by
  unfold LiteralOpeningStages.readSecond LiteralOpeningStages.readFirst
    LiteralOpeningStages.readKappa LiteralOpeningStages.readGamma
  simp only [readAt]

theorem c1At (w : CanonicalCutEnrichedTranscript.Words) (rs : TranscriptRounds)
    (old : LiteralTranscript.C1Word) (read : LiteralTranscript.c1At rs = some old) :
    LiteralTranscript.c1At (reword w rs) = some w.c1 := by
  unfold LiteralTranscript.c1At reword at *
  rw [List.getElem?_map]
  cases h : rs[0]? with
  | none => simp only [h,Option.bind_none,reduceCtorEq] at read
  | some mc =>
    rcases mc with ⟨m,c⟩
    cases m <;> simp_all only [Option.bind_some,Option.map_some,CanonicalCutEnrichedTranscript.enrichMessage,reduceCtorEq]

theorem c2At (w : CanonicalCutEnrichedTranscript.Words) (rs : TranscriptRounds)
    (old : LiteralTranscript.C2Word) (read : LiteralTranscript.c2At rs = some old) :
    LiteralTranscript.c2At (reword w rs) = some w.c2 := by
  unfold LiteralTranscript.c2At reword at *
  rw [List.getElem?_map]
  cases h : rs[2]? with
  | none => simp only [h,Option.bind_none,reduceCtorEq] at read
  | some mc =>
    rcases mc with ⟨m,c⟩
    cases m <;> simp_all only [Option.bind_some,Option.map_some,CanonicalCutEnrichedTranscript.enrichMessage,reduceCtorEq]

theorem vAt (w : CanonicalCutEnrichedTranscript.Words) (rs : TranscriptRounds)
    (old : LiteralTranscript.VWord) (read : LiteralTranscript.vAt rs = some old) :
    LiteralTranscript.vAt (reword w rs) = some w.final := by
  unfold LiteralTranscript.vAt reword at *
  rw [List.getElem?_map]
  cases h : rs[30]? with
  | none => simp only [h,Option.bind_none,reduceCtorEq] at read
  | some mc =>
    rcases mc with ⟨m,c⟩
    cases m <;> simp_all only [Option.bind_some,Option.map_some,CanonicalCutEnrichedTranscript.enrichMessage,reduceCtorEq]

/-- Successful parsing survives changing unobserved whole-word metadata. -/
theorem semantic_success (w : CanonicalCutEnrichedTranscript.Words) (offset : Nat)
    (rs : TranscriptRounds) (xs : List (R0P.Mask.SemMsgZ E × E))
    (read : LiteralSemanticPrefix.read LiteralOpeningView.eK offset rs = some xs) :
    ∃ ys, LiteralSemanticPrefix.read LiteralOpeningView.eK offset (reword w rs) = some ys ∧
      scalarPairs ys = scalarPairs xs := by
  have same := read_scalar w offset rs
  rw [read] at same
  cases hr : LiteralSemanticPrefix.read LiteralOpeningView.eK offset (reword w rs) with
  | none => change Option.map scalarPairs (none : Option (List _)) = some _ at same; cases same
  | some ys => exact ⟨ys,rfl,Option.some.inj same⟩

#print axioms reword_take
#print axioms erased
#print axioms ordinaryAt
#print axioms readAt
#print axioms readSecond
#print axioms c1At
#print axioms c2At
#print axioms vAt
#print axioms semantic_success
end AspisR1.OraclePortReaderPlumbingC6
end
