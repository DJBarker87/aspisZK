import RPt_FJl_WordLane
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_WordTails
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
open ExactLeafFieldCodec MixedLeafEncoding
abbrev E := AspisWideTower.WideExact

theorem c1 (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data E) (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (j : Fin 22) (s : Fin 4) (c : C1)
    (decoded : TypedRecoveredWords.decodeC1At (fun i=>packed parsed q 0 i.val) (q j)=some c) :
    data.W 28 (AspisR1.childIndex (q j) s)=LiteralOpeningView.eK (c s).2 := by
  rw [FJl_LiteralW.value parsed q tr data read]
  change TypedRecoveredWords.word ExactBaseProjection.embed LiteralOpeningView.eK
    (fun i=>packed parsed q 0 i.val) (fun i=>packed parsed q 1 i.val) _ _=_
  have h := TypedRecoveredWords.word_c1_tail_of_decode ExactBaseProjection.embed LiteralOpeningView.eK
    (fun i=>packed parsed q 0 i.val) (fun i=>packed parsed q 1 i.val)
    (AspisR1.childIndex (q j) s) c (by rw [FJl_WordLane.leaf];exact decoded)
  simpa only [FJl_WordLane.slot,show (⟨28,by decide⟩ : Fin 29)=28 from by decide] using h

theorem c2first (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data E) (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (j : Fin 22) (s : Fin 4) (c : C2)
    (decoded : TypedRecoveredWords.decodeC2At (fun i=>packed parsed q 1 i.val) (q j)=some c) :
    data.W 26 (AspisR1.childIndex (q j) s)=LiteralOpeningView.eK (c s 0) := by
  rw [FJl_LiteralW.value parsed q tr data read]
  change TypedRecoveredWords.word ExactBaseProjection.embed LiteralOpeningView.eK
    (fun i=>packed parsed q 0 i.val) (fun i=>packed parsed q 1 i.val) _ _=_
  have h := TypedRecoveredWords.word_c2_first_of_decode ExactBaseProjection.embed LiteralOpeningView.eK
    (fun i=>packed parsed q 0 i.val) (fun i=>packed parsed q 1 i.val)
    (AspisR1.childIndex (q j) s) c (by rw [FJl_WordLane.leaf];exact decoded)
  simpa only [FJl_WordLane.slot,show (⟨26,by decide⟩ : Fin 29)=26 from by decide,
    show (⟨0,by decide⟩ : Fin 2)=0 from by decide] using h

theorem c2second (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data E) (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (j : Fin 22) (s : Fin 4) (c : C2)
    (decoded : TypedRecoveredWords.decodeC2At (fun i=>packed parsed q 1 i.val) (q j)=some c) :
    data.W 27 (AspisR1.childIndex (q j) s)=LiteralOpeningView.eK (c s 1) := by
  rw [FJl_LiteralW.value parsed q tr data read]
  change TypedRecoveredWords.word ExactBaseProjection.embed LiteralOpeningView.eK
    (fun i=>packed parsed q 0 i.val) (fun i=>packed parsed q 1 i.val) _ _=_
  have h := TypedRecoveredWords.word_c2_second_of_decode ExactBaseProjection.embed LiteralOpeningView.eK
    (fun i=>packed parsed q 0 i.val) (fun i=>packed parsed q 1 i.val)
    (AspisR1.childIndex (q j) s) c (by rw [FJl_WordLane.leaf];exact decoded)
  simpa only [FJl_WordLane.slot,show (⟨27,by decide⟩ : Fin 29)=27 from by decide,
    show (⟨1,by decide⟩ : Fin 2)=1 from by decide] using h
#print axioms c1
#print axioms c2first
#print axioms c2second
end AspisR1.FJl_WordTails
end
