import NLK_LaneInvocation
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NLK_LaneInstall
open Aeneas Aeneas.Std Result
/-- Value-slot selection only. The full native allocation interpretation is
NLK_LaneInvocation.owned, and native schema association is separately reviewed.
This theorem is NOT premise removal or a native-row certificate by itself. -/
def bind {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E) :=
 {missing with adapter := {missing.adapter with op50:=NLK_LaneProgram.reference}}

theorem actual_slot {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E)
 (devnet : Bool) (indexError : E) (r : AspisR1.NP6_StdModel.Reservation) :
 (NHJ_DeployedIds.configuration (bind missing) devnet indexError r).adapter.op50=
 NLK_LaneProgram.reference := rfl

theorem frame {E : Type} (missing : AspisR1.IDa_Deployed.Uninstalled E) :
 (bind missing).adapter.op43=missing.adapter.op43 ∧
 (bind missing).adapter.op44=missing.adapter.op44 ∧
 (bind missing).adapter.op48=missing.adapter.op48 ∧
 (bind missing).adapter.op49=missing.adapter.op49 := ⟨rfl,rfl,rfl,rfl⟩

#print actual_slot
#print axioms actual_slot
#print axioms frame
end NLK_LaneInstall
