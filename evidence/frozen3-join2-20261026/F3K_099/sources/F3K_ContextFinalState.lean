import F3K_InputFinalState
import OraclePortAcceptedContextC6
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_ContextFinalState
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem input (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : RecordedBinaryExperimentBin.SourceInputs)
    (v : LiteralOpeningView.View)
    (found : OraclePortStoredDecisionDraftC4.input p q tr=some i)
    (length : tr.rounds.length=33) :
    (OraclePortAcceptedContextC6.context p i v).state=
      UnifiedSampler.stateOf SelectedTranscriptParams.params tr := by
  exact (F3K_InputFinalState.fields tr i
    (OraclePortStoredDecisionDraftC4.input_fields p q tr i found).1 length).symm

#print axioms input
end AspisR1.F3K_ContextFinalState
end
