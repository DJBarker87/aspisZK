import F3K_ProtocolProjection
import OraclePortStoredDecisionDraftC4
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_InputFinalState
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem fields (tr : RawCutTranscriptRun.ErasedPrefix)
    (i : RecordedBinaryExperimentBin.SourceInputs)
    (h : D0InstanceAdmission.Fields tr i) (length : tr.rounds.length=33) :
    UnifiedSampler.stateOf SelectedTranscriptParams.params tr=i.state32 := by
  have last := h.2.2.1
  unfold UnifiedSampler.stateOf
  rw [List.getLast?_eq_getElem?,length]
  rw [show 33-1=32 from rfl,last]

#print axioms fields
end AspisR1.F3K_InputFinalState
end
