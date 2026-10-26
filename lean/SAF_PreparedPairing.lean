import Port4D_Pairing
import SAF_SavedIdentities
import Tx2N_Reader
import OraclePortAcceptedContextC6

set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_PreparedPairing
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open OraclePortCheckpointResumeC5
variable {W : Type}

/-- The three non-arithmetic PairingLaws fields follow from the actual saved
checkpoint decoder's field theorem on the literal accepted Context. -/
theorem identities (p : verifier.Prepared) (a : verifier.Accumulator)
    (parsed : OraclePortCompactDraft.Parsed) (i : RecordedBinaryExperimentBin.SourceInputs)
    (view : LiteralOpeningView.View) (q : Fin 22 → Fin 262144)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K AspisWideTower.WideExact)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a
      (prepared (OraclePortAcceptedContextC6.context parsed i view) i.data
        (SelectedChallengeMap.rhoOf i.rho) q) am) :
    CheckpointBytes5Output.ofE p.claim =
      JointFunctionalBinding.claimedValue i.data.Y i.data.c0 i.data.gamma i.data.kappa ∧
    (∀ x, Array.index_usize p.alpha 0#usize = ok x → CheckpointBytes5Output.ofE x = i.data.alpha0) ∧
    (∀ x, Array.index_usize p.alpha 1#usize = ok x → CheckpointBytes5Output.ofE x = i.data.alpha1) := by
  have saved := SAF_SavedIdentities.fields p a _ am fields
  simpa only [prepared,OraclePortAcceptedContextC6.context,Fin.val_zero,Fin.val_one,
    if_pos rfl,ite_true,show ¬ (1 : Nat) = 0 by decide,if_false] using saved

#print axioms identities
end AspisR1.SAF_PreparedPairing
end
