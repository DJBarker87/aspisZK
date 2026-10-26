import RPz7_F3S_ModelLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_InputAtSecond
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
 theorem facts (p : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : RecordedBinaryExperimentBin.SourceInputs) (wire : AspisV8R19.DuplexFrames.Bytes)
    (same : p.wire=wire) (found : input p q tr=some i) (queries : OraclePortSelectedDraft.queries tr=some q) :
    p=(⟨wire,p.semantic⟩ : Parsed) ∧
    LiteralMatchingData.read (typedRows p q tr)=some i.data ∧
    LiteralQueryRead.decode i.queryBytes=some q := by
  have fields := input_fields p q tr i found
  refine ⟨?_,fields.2,?_⟩
  · cases p
    simp only at same ⊢
    cases same
    rfl
  · simpa only [OraclePortSelectedDraft.queries,fields.1.2.1,Bind.bind,Option.bind] using queries
#print axioms facts
end AspisR1.F3S_InputAtSecond
end
