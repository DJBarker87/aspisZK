import RowFinish_Control
import Port4D_ReturnedFinish
import RowFinish_Finalization

set_option autoImplicit false
noncomputable section
namespace AspisR1.FinT_Returned
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control
attribute [local instance] Classical.propDecidable
attribute [local irreducible] QueryAccumulator.run QueryAccumulator.run22
  QueryResidualBridge.values QueryResidualBridge.basis
  OraclePortCheckpointStateC3.write OraclePortCheckpointStateC3.advance
variable {W : Type}

/-- State identification uses the same saved state and its twelve-step return;
there is no independently chosen complete accumulator. -/
theorem returned_state (i : SourceInputs) (q : Fin 22 → Fin 262144)
    (saved a : verifier.Accumulator)
    (saved_ten : CheckpointBytes5Output.accumulator saved =
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator)
    (twelve : CheckpointBytes5Output.accumulator a =
      OraclePortCheckpointStateC3.advance (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q) 12 (CheckpointBytes5Output.accumulator saved)) :
    CheckpointBytes5Output.accumulator a = OraclePortFrozen2.completeState i q := by
  rw [twelve,saved_ten]
  let model := OraclePortCheckpointResumeC5.model i.data (SelectedChallengeMap.rhoOf i.rho) q
  have eq := (OraclePortCheckpointStateC3.resumed_state model).2
  have prep : (OraclePortCheckpointStateC3.write model).prepared = model := by
    unfold OraclePortCheckpointStateC3.write
    rfl
  simp only [OraclePortCheckpointStateC3.resume,prep] at eq
  simpa only [model,OraclePortCheckpointResumeC5.model,OraclePortCheckpointStateC3.fromData,
    OraclePortFrozen2.completeState] using eq

#print axioms returned_state
end AspisR1.FinT_Returned
end
