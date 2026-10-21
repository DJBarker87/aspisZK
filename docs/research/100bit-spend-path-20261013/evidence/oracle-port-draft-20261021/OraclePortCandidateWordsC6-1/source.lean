import OraclePortMapObservationsC6

set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCandidateWordsC6
open LiteralAcceptanceTerminal
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
attribute [local irreducible] LiteralTypedWords.word

theorem c1_annotation (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (w : LiteralTranscript.C1Word)
    (read : LiteralTranscript.c1At (typedRows p q tr) = some w) : w = (words p q).c1 := by
  unfold LiteralTranscript.c1At typedRows at read
  rw [List.getElem?_mapIdx] at read
  cases h : tr.rounds[0]? with
  | none => simp only [h,Option.map_none,Option.bind_none,reduceCtorEq] at read
  | some mc =>
    rcases mc with ⟨m,c⟩
    cases m <;> simp only [h,Option.map_some,Option.bind_some,restore,reduceCtorEq] at read
    exact read.symm

theorem c2_annotation (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (w : LiteralTranscript.C2Word)
    (read : LiteralTranscript.c2At (typedRows p q tr) = some w) : w = (words p q).c2 := by
  unfold LiteralTranscript.c2At typedRows at read
  rw [List.getElem?_mapIdx] at read
  cases h : tr.rounds[2]? with
  | none => simp only [h,Option.map_none,Option.bind_none,reduceCtorEq] at read
  | some mc =>
    rcases mc with ⟨m,c⟩
    cases m <;> simp only [h,Option.map_some,Option.bind_some,restore,if_pos rfl,reduceCtorEq,Option.some.injEq] at read
    exact read.symm

theorem final_annotation (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (w : LiteralTranscript.VWord)
    (read : LiteralTranscript.vAt (typedRows p q tr) = some w) : w = (words p q).final := by
  unfold LiteralTranscript.vAt typedRows at read
  rw [List.getElem?_mapIdx] at read
  cases h : tr.rounds[30]? with
  | none => simp only [h,Option.map_none,Option.bind_none,reduceCtorEq] at read
  | some mc =>
    rcases mc with ⟨m,c⟩
    cases m <;> simp only [h,Option.map_some,Option.bind_some,restore,
      if_neg (show (30:Nat) ≠ 2 by decide),if_pos rfl,reduceCtorEq,Option.some.injEq] at read
    exact read.symm

theorem reader_words (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (d : MatchingSupport.Data E)
    (read : LiteralMatchingData.read (typedRows p q tr) = some d) :
    d.W = LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
      (words p q).c1 (words p q).c2 ∧ d.V = (words p q).final := by
  obtain ⟨common,staged,row31,word,gamma,kappa,alpha0,alpha1,
    hopen,_,_,hword,_,_,_,_,hdata⟩ := LiteralMatchingFacts.read_success_components _ d read
  obtain ⟨c1,c2,_,w⟩ := LiteralOpeningFunctionalFacts.read_semantic_components _ common hopen
  have h1 := c1_annotation p q tr common.c1 c1
  have h2 := c2_annotation p q tr common.c2 c2
  have hf := final_annotation p q tr word hword
  rw [hdata]
  change common.word = _ ∧ word = _
  exact ⟨w.trans (by rw [h1,h2]),hf⟩

#print axioms c1_annotation
#print axioms c2_annotation
#print axioms final_annotation
#print axioms reader_words
end AspisR1.OraclePortCandidateWordsC6
end
