import NKF_MasterBox
import NKF_CheckpointBox
set_option autoImplicit false
noncomputable section
namespace NKF_BoxInstall
open Aeneas Aeneas.Std Result
/-- Installation/realization only; this does not claim removal of any premise. -/
def bind {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E) :=
 {missing with adapter := {missing.adapter with
   op48 := NKF_MasterBox.reference
   op49 := NKF_CheckpointBox.reference}}

theorem actual_slots {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
 (devnet : Bool) (indexError : E) (reservation : AspisR1.NP6_StdModel.Reservation) :
 (NHJ_DeployedIds.configuration (bind missing) devnet indexError reservation).adapter.op48 = NKF_MasterBox.reference ∧
 (NHJ_DeployedIds.configuration (bind missing) devnet indexError reservation).adapter.op49 = NKF_CheckpointBox.reference := ⟨rfl,rfl⟩

theorem digest_error_frame {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E) :
 (bind missing).adapter.op43 = missing.adapter.op43 ∧
 (bind missing).adapter.op44 = missing.adapter.op44 ∧
 (bind missing).adapter.op50 = missing.adapter.op50 := ⟨rfl,rfl,rfl⟩
set_option pp.proofs false in
#print actual_slots
#print axioms actual_slots
#print axioms digest_error_frame
end NKF_BoxInstall
