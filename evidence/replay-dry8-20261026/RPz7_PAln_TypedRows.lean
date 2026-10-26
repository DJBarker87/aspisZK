import RPz7_PAln_Transcript
import RPz7_PAln_SemanticRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_TypedRows
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun
open PAln_Transcript

theorem entry (p : Parsed) (q : Fin 22 → Fin 262144) (pub : LiteralTranscript.Public)
    (root : State) (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (challenge : Nat → LiteralTranscript.Challenge) (row : Nat) (below : row<33) :
    (typedRows p q (transcript p pub root bound challenge))[row]?=
      some (restore (words p q) row (message p root bound row),challenge row) := by
  simp only [typedRows,List.getElem?_mapIdx,PAln_Transcript.entry p pub root bound challenge row below,Option.map_some]

theorem valid (p : Parsed) (q : Fin 22 → Fin 262144) (root : State)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (row : Nat) (below : row<33) :
    LiteralTranscript.valid row (restore (words p q) row (message p root bound row)) := by
  by_cases zero : row=0
  · subst row
    simp [message,restore,LiteralTranscript.valid]
  · by_cases two : row=2
    · subst row; simp [message,restore,LiteralTranscript.valid]
    · by_cases thirty : row=30
      · subst row; simp [message,restore,LiteralTranscript.valid]
      · simp [message,restore,LiteralTranscript.valid,zero,two,thirty,below]

theorem record_restore (w : CanonicalCutEnrichedTranscript.Words) (row : Nat) (m : ErasedMessage) :
    LiteralSemanticCodecBridge.record (restore w row m)=
      match m with | .initial _ => PublicInitFrame.emptyRecord | .payload b => b.val := by
  cases m with
  | initial root => rfl
  | payload b =>
    by_cases two : row=2 <;> by_cases thirty : row=30 <;>
      simp [restore,two,thirty,LiteralSemanticCodecBridge.record]

#print axioms entry
#print axioms valid
#print axioms record_restore
end AspisR1.PAln_TypedRows
end
