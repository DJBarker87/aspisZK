import Port4D_FinishFrozen
import Port4D_Pairing
import OraclePortFrozen2Checkpoint
import Port4D_FlushRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4D_ReturnedFinish
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] QueryAccumulator.run QueryAccumulator.run22 QueryResidualBridge.values QueryResidualBridge.basis OraclePortCheckpointStateC3.write OraclePortCheckpointStateC3.advance
variable {W : Type}

/-- Accepted source verdict equals Frozen2 finish on the SAME actual returned
state. Saved-ten provenance and twelve-step interpretation are separate row
ports; this theorem composes them symbolically rather than assuming run22.
Session A's S3/S4/S5/S9 arithmetic leaves remain named hypotheses. -/
theorem accepted_twelve (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs)
    (s2 : p.variant = .S2)
    (read : LiteralMatchingData.read (typedRows parsed q tr) = some i.data)
    (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (pairing_S3_S5_S9 : Port4D_Pairing.PairingLaws (Port3_FinishStage.release ops)
      CheckpointBytes5Output.ofE v p i.data)
    (matches_S4_S7 : ∀ j, MatchingSupport.match0 i.data (q j))
    (semantic_S3_S9 : R3SemanticRemainingJoins.EquationEndpoint i.decoded
      (typedRows parsed q tr) i.data)
    (dot_S5 : ∀ actual, ops.dot v.final_message a.weights.deref = ok (.Ok actual) →
      CheckpointBytes5Output.ofE actual = ∑ l : Fin 64, i.data.f l * LiteralOpeningView.eK
        ((CheckpointBytes5Output.accumulator a).weights l))
    (saved : verifier.Accumulator)
    (saved_ten : CheckpointBytes5Output.accumulator saved =
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator)
    (twelve : CheckpointBytes5Output.accumulator a =
      OraclePortCheckpointStateC3.advance (OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q) 12
        (CheckpointBytes5Output.accumulator saved))
    (success : Port4D_FinishInstall.finish ops v p a none = ok (.Ok ())) :
    ops.dot v.final_message a.weights.deref =
      ok (.Ok a.rhs) ∧
    a.next = 22#usize ∧
    decide (Port4D_FinishInstall.finish ops v p a none = ok (.Ok ())) =
      OraclePortFrozen2.finish parsed q tr i (CheckpointBytes5Output.accumulator a) := by
  have returned : CheckpointBytes5Output.accumulator a = OraclePortFrozen2.completeState i q := by
    rw [twelve,saved_ten]
    let model := OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q
    have eq := (OraclePortCheckpointStateC3.resumed_state model).2
    have prep : (OraclePortCheckpointStateC3.write model).prepared = model := by
      unfold OraclePortCheckpointStateC3.write
      rfl
    simp only [OraclePortCheckpointStateC3.resume,prep] at eq
    simpa only [model,OraclePortCheckpointResumeC5.model,OraclePortCheckpointStateC3.fromData,
      OraclePortFrozen2.completeState] using eq
  obtain ⟨dot,next,accepted⟩ := Port4D_FinishFrozen.accepted_finish ops v p a parsed q tr i
    s2 read decoded pairing_S3_S5_S9 matches_S4_S7 semantic_S3_S9 dot_S5 returned success
  refine ⟨dot,next,?_⟩
  rw [accepted]
  exact decide_eq_true success

#print axioms accepted_twelve
end AspisR1.Port4D_ReturnedFinish
end
