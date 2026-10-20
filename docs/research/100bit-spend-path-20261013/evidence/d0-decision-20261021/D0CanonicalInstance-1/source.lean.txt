import D0InstanceAdmission

/-! R16 is constructed on admitted canonical runs. No word-recovery premise
is used: R16 itself needs only public parsing and the late row placements. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.D0CanonicalInstance
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin
open DecoderInstanceBoundaryBin
attribute [local instance] Classical.propDecidable

/-- Compilation preserves the entire erased prefix supplied to a decision. -/
theorem compiled_erasure (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
      (compiledPublic D d P H) (annotatedRun D d P H).2.1.2 33) =
    LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
      (eval H P).2.1 (eval H P).2.2 33) := by
  unfold compiledPublic annotatedRun
  rw [compiled_experiment_eval]
  dsimp only
  rw [RawCutTranscriptRun.transcript_eq,
    CanonicalCutEnrichedTranscript.erasePrefix_enrich]
  rw [RawCutProverCompiler.experiment_eval]

/-- Admission plus the canonical reduction constructs all R16 instance fields
for every accepted original prover, with no constructor restriction on P. -/
theorem accepted_instance (D : LiteralByteProtocol.Decoder)
    (core : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (accepted : FS2.accepts (eval H
      (original D (D0InstanceAdmission.verify core) P))) :
    ∃ i : SourceInputs, InstanceFields D (D0InstanceAdmission.verify core)
      (R16CanonReduction.canon P) H i := by
  let d := D0InstanceAdmission.verify core
  have dec : d
      (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
        (eval H P).2.1 (eval H P).2.2 33))
      (LiteralTranscript.erase ((eval H P).2.2 33)) = true := by
    change (eval H (original D d P)).2.2 = true at accepted
    rw [RawCutProverCompiler.experiment_eval, RawCutProverCompiler.verifier,
      FS2.verifier_eval] at accepted
    exact accepted
  obtain ⟨i, fields⟩ := D0InstanceAdmission.accepted_fields core _ _ dec
  have prefixSame := compiled_erasure D d (R16CanonReduction.canon P) H
  rw [R16CanonReduction.eval_canon] at prefixSame
  dsimp only at prefixSame
  have canonicalSame := R16DecisionErasure.erased_transcript_eq D H
    (eval H P).2.1 (eval H P).2.2 (R16CanonReduction.proof (eval H P).2.2)
    (R16CanonReduction.erase_proof _) 33
  have fields' : D0InstanceAdmission.Fields
      (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
        (compiledPublic D d (R16CanonReduction.canon P) H)
        (annotatedRun D d (R16CanonReduction.canon P) H).2.1.2 33)) i := by
    rw [prefixSame, canonicalSame]
    exact fields
  have valid := D0ScheduleAdmission.accepted_canon_prover_valid D
    (fun p m => decide (∃ i, D0InstanceAdmission.Fields p i) && core p m) P H accepted
  have compiledValid : ∀ row, row < 33 → LiteralTranscript.valid row
      ((annotatedRun D d (R16CanonReduction.canon P) H).2.1.2 row) := by
    intro row hr
    unfold annotatedRun
    rw [compiled_experiment_eval]
    apply D0ScheduleAdmission.enrich_valid
    rw [R16CanonRecorded.original_proof]
    exact valid row hr
  exact ⟨i, D0InstanceAdmission.fields_to_instance D d (R16CanonReduction.canon P) H
    i fields' (compiledValid 31 (by decide)) (compiledValid 32 (by decide))⟩

#print axioms compiled_erasure
#print axioms accepted_instance
end AspisR1.D0CanonicalInstance
end
