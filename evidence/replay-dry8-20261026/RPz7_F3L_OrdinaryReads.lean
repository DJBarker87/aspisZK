import RPz7_F3L_SamplerOrdinary
import RPz7_F3L_SamplerAt
import RPz7_F3L_EraseIndex
import F3L_RestoreChallenge
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_OrdinaryReads
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft
attribute [local irreducible] F3J_InputRows.proof F3J_SamplerRun.program

theorem read (H : Bytes → State) (p : Parsed) (root : State)
    (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (pub : LiteralTranscript.Public) (q : Fin 22 → Fin 262144) (row : Nat) (below : row<31) :
    ∃ value,LiteralChallengeRead.ordinaryAt (OraclePortStoredDecisionDraftC4.typedRows p q
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program
        (F3J_InputRows.proof p root w bound) 0 33 (FS.emptyPrefix pub))).2)) row=some value := by
  let pf := F3J_InputRows.proof p root w bound
  let P := (eval H (F3J_SamplerRun.program pf 0 row (FS.emptyPrefix pub))).2
  let ch := (eval H (LiteralByteSampler.samp row P (pf row)).toProgram).2
  have ordinary : ∃ value,ch.1=TranscriptView.Value.ordinary value := by
    by_cases zero : row=0
    · subst row
      exact F3L_SamplerOrdinary.initial H P (pf 0) root
        (by rw [F3J_InputRows.erased,if_pos rfl])
    · exact F3L_SamplerOrdinary.payload H P (pf row) ⟨rowBytes p row,bound row⟩ row zero
        (by omega) (by rw [F3J_InputRows.erased,if_neg zero])
  obtain ⟨value,tag⟩ := ordinary
  have chEq : ch=(TranscriptView.Value.ordinary value,ch.2) := Prod.ext tag rfl
  have e := F3L_SamplerAt.entry H pf 0 row (33-row-1) (FS.emptyPrefix pub)
  have total : row+(33-row-1+1)=33 := by omega
  simp only [FS.emptyPrefix,List.length_nil,Nat.zero_add,total] at e
  have typed := e.trans (congrArg (fun c=>some (pf row,c)) chEq)
  have erased := F3L_EraseIndex.entry _ row _ _ typed
  exact ⟨value,F3L_RestoreChallenge.ordinary p q _ row _ value ch.2 erased⟩

#print axioms read
end AspisR1.F3L_OrdinaryReads
end
