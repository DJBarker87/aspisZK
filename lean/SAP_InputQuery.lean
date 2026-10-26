import OraclePortStoredDecisionDraftC4
set_option autoImplicit false
namespace AspisR1.SAP_InputQuery
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4

theorem decoded (p : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (q : Fin 22 → Fin 262144) (i : RecordedBinaryExperimentBin.SourceInputs)
    (found : input p q tr=some i) (selected : OraclePortSelectedDraft.queries tr=some q) :
    LiteralQueryRead.decode i.queryBytes=some q := by
  have fields := (input_fields p q tr i found).1
  unfold OraclePortSelectedDraft.queries at selected
  rw [fields.2.1] at selected
  exact selected

#print axioms decoded
end AspisR1.SAP_InputQuery
