import OraclePortCkptAbiReference
import OraclePortFrozenOrderAccepted

/-! Identify the saved recurrence inputs from the accepted frozen decision.
This is model provenance. Identification of the Rust preparation/query-loop
and retained semantic context remains a separate source obligation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCkptAbi2Reached
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortCheckpointResumeC5
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
open RecordedBinaryExperimentBin (SourceInputs)

/-- Query uniqueness is derived from the actual reached sampler row, rather
than assumed for an externally supplied saved state. -/
theorem accepted_inputs (stored : Bytes) (tr : ErasedPrefix) (m : ErasedMessage)
    (H : Bytes → State)
    (accepted : (eval H (OraclePortFrozenOrder.dV_frozen stored tr m)).2 = true) :
    ∃ p q i, OraclePortStoredParserC4.parseReached stored tr = some p ∧
      queries tr = some q ∧ OraclePortStoredDecisionDraftC4.input p q tr = some i ∧
      D0InstanceAdmission.Fields tr i ∧
      LiteralMatchingData.read (OraclePortStoredDecisionDraftC4.typedRows p q tr) = some i.data ∧
      LiteralQueryRead.decode i.queryBytes = some q ∧ Function.Injective q := by
  obtain ⟨_,p,q,i,hp,hq,_,hi,_⟩ := OraclePortFrozenOrder.accepted_details stored tr m H accepted
  obtain ⟨fields,data⟩ := OraclePortStoredDecisionDraftC4.input_fields p q tr i hi
  have decoded : LiteralQueryRead.decode i.queryBytes = some q := by
    simpa [queries,fields.2.1] using hq
  exact ⟨p,q,i,hp,hq,hi,fields,data,decoded,(LiteralQueryRead.decode_success _ _ decoded).2⟩

/-- Total reference resume of the reached model's saved-ten state. The only
remaining Context argument is explicit; no Rust context equality is invented. -/
theorem accepted_reference_resume (stored pub : Bytes) (tr : ErasedPrefix)
    (m : ErasedMessage) (H : Bytes → State)
    (accepted : (eval H (OraclePortFrozenOrder.dV_frozen stored tr m)).2 = true) :
    ∃ p q i, OraclePortStoredParserC4.parseReached stored tr = some p ∧
      queries tr = some q ∧ OraclePortStoredDecisionDraftC4.input p q tr = some i ∧
      ∀ c : Context,
        (eval H (OraclePortCkptAbiReference.resume stored pub
          (save H stored pub c i.data (SelectedChallengeMap.rhoOf i.rho) q).checkpoint)).2 =
          some (prepared c i.data (SelectedChallengeMap.rhoOf i.rho) q,
            (OraclePortCheckpointStateC3.write
              (model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator) := by
  obtain ⟨p,q,i,hp,hq,hi,_,_,_,unique⟩ := accepted_inputs stored tr m H accepted
  refine ⟨p,q,i,hp,hq,hi,?_⟩
  intro c
  rw [OraclePortCkptAbiReference.resume_saved,if_pos unique]

#print axioms accepted_inputs
#print axioms accepted_reference_resume
end AspisR1.OraclePortCkptAbi2Reached
end
