import R16DecisionErasure

/-! The requested R19 decision-only specialisation is impossible at its
unchanged arbitrary-Prover interface. No premise-removing soundness theorem
is claimed. Canonical constructor admission must be owned by the model first. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R1FinalSoundnessBinPerQueryDecision
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin
abbrev BoundaryStatements := R1FinalSoundness.BoundaryStatements
abbrev BoundaryEvidence := R1FinalSoundness.BoundaryEvidence

/-- A nonempty accepted language and the requested universal R16 construction
are inconsistent. Source selection is allowed to depend on P and H, so this
also rules out every more restrictive deterministic source construction. -/
theorem no_nonvacuous_specialisation
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (s : BoundaryStatements) (evidence : BoundaryEvidence s)
    (nonvacuous : ∃ (H : Bytes → State) (pub : LiteralTranscript.Public)
      (pf : LiteralProtocol.Proof),
      (eval H (RawCutProverCompiler.verifier D d pub pf)).2 = true) :
    ¬ (∀ P : Prover, ∃ source : (Bytes → State) → SourceInputs,
      BoundaryEvidence s → ∀ H,
        FS2.accepts (eval H (original D d P)) →
          InstanceFields D d P H (source H)) := by
  intro construction
  obtain ⟨H, pub, pf, accepted⟩ := nonvacuous
  obtain ⟨source, law⟩ := construction (Program.done (pub, R16DecisionErasure.retagProof pf))
  obtain ⟨ha, hn⟩ := R16DecisionErasure.accepted_without_instance D d H pub pf accepted
  exact hn (source H) (law evidence H ha)

/-- Concrete free-decision counterexample: the acceptance premise is proved,
not assumed. The retagged row defeats every possible source selection. -/
theorem true_decision_counterexample
    (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) :
    let d : ErasedPrefix → ErasedMessage → Bool := fun _ _ => true
    let P : Prover := Program.done (pub, R16DecisionErasure.retagProof pf)
    FS2.accepts (eval H (original D d P)) ∧
      ∀ i : SourceInputs, ¬ InstanceFields D d P H i := by
  apply R16DecisionErasure.accepted_without_instance
  unfold RawCutProverCompiler.verifier
  rw [FS2.verifier_eval]
  rfl

#print axioms no_nonvacuous_specialisation
#print axioms true_decision_counterexample
end AspisR1.R1FinalSoundnessBinPerQueryDecision
end
