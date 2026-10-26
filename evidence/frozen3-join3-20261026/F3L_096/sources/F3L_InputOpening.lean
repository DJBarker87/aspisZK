import F3L_MatchingChallenges
import OraclePortStoredDecisionDraftC4
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_InputOpening

theorem exists_view (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : RecordedBinaryExperimentBin.SourceInputs)
    (found : OraclePortStoredDecisionDraftC4.input p q tr=some i) :
    ∃ v,LiteralOpeningView.read (OraclePortStoredDecisionDraftC4.typedRows p q tr)=some v := by
  have read := (OraclePortStoredDecisionDraftC4.input_fields p q tr i found).2
  obtain ⟨common,_,_,_,_,_,_,_,view,_⟩ := PAln_MatchingFacts.read_success_components _ i.data read
  exact ⟨common,view⟩

#print axioms exists_view
end AspisR1.F3L_InputOpening
end
