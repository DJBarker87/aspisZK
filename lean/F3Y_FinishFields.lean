import F3Y_PreparedScalars
import OraclePortAcceptedContextC6
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Y_FinishFields
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCheckpointAbiC5 OraclePortCheckpointResumeC5
attribute [local irreducible] JointFunctionalBinding.claimedValue

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
  have result := F3Y_PreparedScalars.values p a _ am fields
  simpa only [Holds,prepared,OraclePortAcceptedContextC6.context,Fin.val_zero,Fin.val_one,
    ite_true,if_pos rfl,if_neg (by decide : ¬(1:Nat)=0)] using result

#print axioms from_fields
end AspisR1.F3Y_FinishFields
end
