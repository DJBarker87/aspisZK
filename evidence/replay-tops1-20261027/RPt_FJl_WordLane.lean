import RPt_FJl_LiteralW
import R1TypedRecoveredWords
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_WordLane
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
open ExactLeafFieldCodec MixedLeafEncoding
abbrev E := AspisWideTower.WideExact

theorem leaf (q : Fin 262144) (s : Fin 4) :
    TypedRecoveredWords.queryLeaf (AspisR1.childIndex q s)=q := by
  apply Fin.ext
  change (4*q.val+s.val)/4=q.val
  have := s.isLt
  omega

theorem slot (q : Fin 262144) (s : Fin 4) :
    TypedRecoveredWords.querySlot (AspisR1.childIndex q s)=s := by
  apply Fin.ext
  change (4*q.val+s.val)%4=s.val
  have := s.isLt
  omega
/-- A scalar coordinate of SAME literal W after strict C1 decoding. -/
theorem scalar (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data E) (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (j : Fin 22) (s : Fin 4) (l : Fin 26) (c : C1)
    (decoded : TypedRecoveredWords.decodeC1At (fun i=>packed parsed q 0 i.val) (q j)=some c) :
    data.W ⟨l.val,by have := l.isLt;omega⟩ (AspisR1.childIndex (q j) s)=
      ExactBaseProjection.embed ((c s).1 l) := by
  rw [FJl_LiteralW.value parsed q tr data read]
  change TypedRecoveredWords.word ExactBaseProjection.embed LiteralOpeningView.eK
    (fun i=>packed parsed q 0 i.val) (fun i=>packed parsed q 1 i.val) _ _=_
  have h := TypedRecoveredWords.word_c1_base_of_decode ExactBaseProjection.embed LiteralOpeningView.eK
    (fun i=>packed parsed q 0 i.val) (fun i=>packed parsed q 1 i.val)
    (AspisR1.childIndex (q j) s) l c (by rw [leaf];exact decoded)
  simpa only [slot] using h
#print axioms leaf
#print axioms slot
#print axioms scalar
end AspisR1.FJl_WordLane
end
