import R1FinalSoundnessHeadline

/-! S2 source/model obstruction. This module deliberately has no final_soundness
wrapper: the frozen header fact cannot identify an arbitrary d or public tag.
It does not claim that the headline with its tag premise deleted is false. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R1FinalSoundnessHeadlineS2
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin

def unconstrainedStatements : R1FinalSoundness.BoundaryStatements where
  P1 := True
  P2 := True
  P2_prime := True
  P3 := True
  P4 := True
  P5 := True
  P6 := True
  P7 := True
  R10 := True
  R22 := True
  R4_transport := True
  R17 := True
  R20 := True
  R21 := True
  S1 := True
  S2 := True
  S3 := True
  S4 := True
  S5 := True
  S6 := True
  S7 := True
  S8 := True
  S9 := True
  S10 := True
  M10_uniform := True

def unconstrainedEvidence : R1FinalSoundness.BoundaryEvidence unconstrainedStatements := by
  constructor <;> trivial

/-- The actual evidence record is inhabited while d violates global tag admission.
This concerns the formal interface, not shipped verifier acceptance. -/
theorem evidence_does_not_identify_decision :
    Nonempty (R1FinalSoundness.BoundaryEvidence unconstrainedStatements) ∧
    ¬ InitialTagDecision.RejectsOtherTags (fun _ _ => true) := by
  refine ⟨⟨unconstrainedEvidence⟩, ?_⟩
  intro h
  have hf := h ⟨⟨[], by decide, 0⟩, []⟩ (.initial default) (by decide)
  cases hf

/-- Exact reachable-domain obstruction: if a clean checked non-2 run exists,
the arbitrary always-true d cannot satisfy CheckedRejects. Existence is explicit;
no malformed transcript is asserted to be format-checked. -/
theorem checked_run_obstruction (D : LiteralByteProtocol.Decoder) (P : Prover)
    (Q : Nat) (H : Bytes → State)
    (hclean : ¬ binaryCollision Q (eval H (recorded D (fun _ _ => true) P)))
    (hformat : RWireCheckedFormat.Format (eval H (recorded D (fun _ _ => true) P)).2.1.2)
    (htag : (InitialTagDecision.finalPrefix D (fun _ _ => true) P H).statement.tag ≠ 2) :
    ¬ InitialTagDecision.CheckedRejects D (fun _ _ => true) P Q := by
  intro h
  have hf := h H hclean hformat htag
  cases hf

/-- An actual binding only on the checked domain suffices. This explicit
interface is NOT inserted into an endpoint or advertised as premise deletion. -/
theorem checked_rejects_of_reachable_binding
    (D : LiteralByteProtocol.Decoder) (d : ErasedPrefix → ErasedMessage → Bool)
    (P : Prover) (Q : Nat)
    (sourceDecision : ErasedPrefix → ErasedMessage → Bool)
    (hsource : InitialTagDecision.RejectsOtherTags sourceDecision)
    (hbinding : ∀ H, ¬ binaryCollision Q (eval H (recorded D d P)) →
      RWireCheckedFormat.Format (eval H (recorded D d P)).2.1.2 →
      d (InitialTagDecision.finalPrefix D d P H) (InitialTagDecision.finalMessage D d P H) =
      sourceDecision (InitialTagDecision.finalPrefix D d P H) (InitialTagDecision.finalMessage D d P H)) :
    InitialTagDecision.CheckedRejects D d P Q := by
  intro H hc hf ht
  rw [hbinding H hc hf]
  exact hsource _ _ ht

#print axioms unconstrainedEvidence
#print axioms evidence_does_not_identify_decision
#print axioms checked_run_obstruction
#print axioms checked_rejects_of_reachable_binding
end AspisR1.R1FinalSoundnessHeadlineS2
end
