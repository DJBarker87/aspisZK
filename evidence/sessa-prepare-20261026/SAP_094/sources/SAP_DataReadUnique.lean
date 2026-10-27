import OraclePortStoredDecisionDraftC4
set_option autoImplicit false
namespace AspisR1.SAP_DataReadUnique
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4

theorem unique (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : RecordedBinaryExperimentBin.SourceInputs)
    (found : input parsed q tr=some i) :
    ∀ data, LiteralMatchingData.read (typedRows parsed q tr)=some data → data=i.data := by
  intro data read
  exact Option.some.inj (read.symm.trans (input_fields parsed q tr i found).2)

#print axioms unique
end AspisR1.SAP_DataReadUnique
