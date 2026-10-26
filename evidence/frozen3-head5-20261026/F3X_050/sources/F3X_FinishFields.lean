import F3N_ReaderNumeric
import OraclePortAcceptedContextC6
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_FinishFields
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5

def Holds (p : verifier.Prepared) (data : MatchingSupport.Data E) : Prop :=
  CheckpointBytes5Output.ofE p.claim=JointFunctionalBinding.claimedValue data.Y data.c0 data.gamma data.kappa ∧
  (∀ x,Array.index_usize p.alpha 0#usize=ok x → CheckpointBytes5Output.ofE x=data.alpha0) ∧
  (∀ x,Array.index_usize p.alpha 1#usize=ok x → CheckpointBytes5Output.ofE x=data.alpha1)

/-- Three former finish-owner families follow from actual authenticated
checkpoint fields, rather than a new owner assertion. -/
theorem from_fields (p : verifier.Prepared) (a : verifier.Accumulator)
    (parsed : OraclePortCompactDraft.Parsed) (data : RecordedBinaryExperimentBin.SourceInputs)
    (view : LiteralOpeningView.View) (q : Fin 22 → Fin 262144) (am : QueryAccumulator.State K E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a
      (prepared (OraclePortAcceptedContextC6.context parsed data view) data.data
        (SelectedChallengeMap.rhoOf data.rho) q) am) : Holds p data.data := by
  refine ⟨?_,?_,?_⟩
  · rw [fields.claim,CheckpointBytes5Output.ofE_source]
    rfl
  · intro x read
    have actual : Array.index_usize p.alpha 0#usize=ok (CheckpointBytes4ReaderFields.sourceE data.data.alpha0) := by
      simp [Array.index_usize,fields.alpha,prepared]
    have same := Result.ok.inj (read.symm.trans actual)
    rw [same,CheckpointBytes5Output.ofE_source]
  · intro x read
    have actual : Array.index_usize p.alpha 1#usize=ok (CheckpointBytes4ReaderFields.sourceE data.data.alpha1) := by
      simp [Array.index_usize,fields.alpha,prepared]
    have same := Result.ok.inj (read.symm.trans actual)
    rw [same,CheckpointBytes5Output.ofE_source]

#print axioms from_fields
end AspisR1.F3X_FinishFields
end
