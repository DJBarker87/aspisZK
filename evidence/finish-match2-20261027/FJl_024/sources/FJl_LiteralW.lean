import FJl_WordRead
import R1LiteralOpeningFunctionalFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_LiteralW
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
/-- Transport the literal W to the two fixed packed maps restored by typedRows. -/
theorem value (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (data : MatchingSupport.Data AspisWideTower.WideExact)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data) :
    data.W=LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
      (words parsed q).c1 (words parsed q).c2 := by
  obtain ⟨common,hread,hw⟩ := FJl_WordRead.value parsed q tr data read
  obtain ⟨hc1,hc2,hs,hword⟩ := LiteralOpeningFunctionalFacts.read_semantic_components _ common hread
  have c1 : common.c1=(words parsed q).c1 := by
    unfold LiteralTranscript.c1At typedRows at hc1
    rw [List.getElem?_mapIdx] at hc1
    cases entry : tr.rounds[0]? with
    | none => simp only [entry,Option.map_none,Option.bind_none,reduceCtorEq] at hc1
    | some mc =>
      rcases mc with ⟨m,c⟩
      cases m with
      | initial root => simpa only [entry,Option.map_some,Option.bind_some,restore,Option.some.injEq] using hc1.symm
      | payload bytes => simp [entry,restore] at hc1
  have c2 : common.c2=(words parsed q).c2 := by
    unfold LiteralTranscript.c2At typedRows at hc2
    rw [List.getElem?_mapIdx] at hc2
    cases entry : tr.rounds[2]? with
    | none => simp only [entry,Option.map_none,Option.bind_none,reduceCtorEq] at hc2
    | some mc =>
      rcases mc with ⟨m,c⟩
      cases m with
      | initial root => simp [entry,restore] at hc2
      | payload bytes => simpa only [entry,Option.map_some,Option.bind_some,restore,ite_true,Option.some.injEq] using hc2.symm
  rw [hw,hword,c1,c2]
#print axioms value
end AspisR1.FJl_LiteralW
end
