import SAP_BindingUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_InputUnique
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5

theorem unique (p : AspisR1CurrentCaller.verifier.Prepared)
    (parsed : Parsed) (tr : RawCutTranscriptRun.ErasedPrefix)
    (i j : RecordedBinaryExperimentBin.SourceInputs)
    (q q' : Fin 22 → Fin 262144) (c c' : Context)
    (found : input parsed q tr=some i) (found' : input parsed q' tr=some j)
    (h : SAP_LiteralFields.Fields p i q c) (h' : SAP_LiteralFields.Fields p j q' c') :
    q=q' ∧ i=j ∧ c=c' := by
  have sameQ := SAP_BindingUnique.queries p i j q q' c c' h h'
  have sameC := SAP_BindingUnique.context p i j q q' c c' h h'
  subst q'
  exact ⟨rfl,Option.some.inj (found.symm.trans found'),sameC⟩

#print axioms unique
end AspisR1.SAP_InputUnique
end
