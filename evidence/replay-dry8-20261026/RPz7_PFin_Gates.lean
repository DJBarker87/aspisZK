import F3L_InputDiscovery
import RPz7_Tx1Q_Endpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_Gates
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4

theorem decoded (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : RecordedBinaryExperimentBin.SourceInputs)
    (found : input p q tr = some i) (queries : OraclePortSelectedDraft.queries tr = some q) :
    LiteralQueryRead.decode i.queryBytes = some q := by
  have fields := (input_fields p q tr i found).1
  unfold OraclePortSelectedDraft.queries at queries
  rw [fields.2.1] at queries
  exact queries

theorem closed (stored : Bytes) (p : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : RecordedBinaryExperimentBin.SourceInputs)
    (parser : OraclePortStoredParserC4.parseReached stored tr = some p)
    (found : input p q tr = some i) (queries : OraclePortSelectedDraft.queries tr = some q) :
    Aligned p tr ∧ LiteralMatchingData.read (typedRows p q tr) = some i.data ∧
      LiteralQueryRead.decode i.queryBytes = some q :=
  ⟨(OraclePortStoredParserC4.parsed stored tr p parser).2.2,
    (input_fields p q tr i found).2,decoded p q tr i found queries⟩

#print axioms decoded
#print axioms closed
end AspisR1.PFin_Gates
end
