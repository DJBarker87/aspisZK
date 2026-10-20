import D0CanonicalInstance

/-! Total source selection for the R16 instance. The fallback supplies only
unconstrained data on rejected executions. Matching/semantic facts about the
selected accepted data are not inferred from instance fields. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.D0CanonicalSource
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin
attribute [local instance] Classical.propDecidable

def source (D : LiteralByteProtocol.Decoder)
    (core : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (fallback : (Bytes → State) → SourceInputs) (H : Bytes → State) : SourceInputs :=
  if h : ∃ i : SourceInputs, InstanceFields D (D0InstanceAdmission.verify core)
      (R16CanonReduction.canon P) H i then Classical.choose h else fallback H

/-- The exact R16 implication for the admitted decision and constructed
source, on canonical P. Original arbitrary-P failure transport is already
proved by D0ScheduleAdmission.arbitrary_prover_reduction. -/
theorem h_R16_instance (D : LiteralByteProtocol.Decoder)
    (core : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (fallback : (Bytes → State) → SourceInputs) (H : Bytes → State)
    (accepted : FS2.accepts (eval H (original D (D0InstanceAdmission.verify core)
      (R16CanonReduction.canon P)))) :
    InstanceFields D (D0InstanceAdmission.verify core) (R16CanonReduction.canon P) H
      (source D core P fallback H) := by
  have originalAccepted : FS2.accepts
      (eval H (original D (D0InstanceAdmission.verify core) P)) := by
    change (eval H (original D (D0InstanceAdmission.verify core)
      (R16CanonReduction.canon P))).2.2 = true at accepted
    rw [R16CanonReduction.original_canon] at accepted
    exact accepted
  have existsInstance := D0CanonicalInstance.accepted_instance D core P H originalAccepted
  simp only [source, dif_pos existsInstance]
  exact Classical.choose_spec existsInstance

#print axioms h_R16_instance
end AspisR1.D0CanonicalSource
end
