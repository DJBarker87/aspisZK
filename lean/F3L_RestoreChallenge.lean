import OraclePortStoredDecisionDraftC4
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_RestoreChallenge

/-- Restoring arithmetic words cannot alter any ordinary challenge. -/
theorem ordinary (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (row : Nat)
    (message : RawCutTranscriptRun.ErasedMessage) (value : LiteralTranscript.E)
    (state : AspisV8R19.SourceDuplexStep.State)
    (entry : tr.rounds[row]?=some (message,(TranscriptView.Value.ordinary value,state))) :
    LiteralChallengeRead.ordinaryAt (OraclePortStoredDecisionDraftC4.typedRows p q tr) row=some value := by
  simp only [LiteralChallengeRead.ordinaryAt,OraclePortStoredDecisionDraftC4.typedRows,
    List.getElem?_mapIdx,entry,Option.map_some,Option.bind_some]

#print axioms ordinary
end AspisR1.F3L_RestoreChallenge
end
