import NND_DecoderSlots
set_option autoImplicit false
noncomputable section
namespace NND_MissingPartial
open Aeneas Aeneas.Std Result AdapterRw AspisR1
/-- Source-linked CLOSED decoder selection. This partial substitution does
not claim to supply TAS.Exhibited: native217, runtime slots, and the remaining
Pool/statement helpers must still be installed and transported. -/
def select {E : Type} (missing : IDa_Deployed.Uninstalled E) : IDa_Deployed.Uninstalled E :=
 {missing with adapter := NND_DecoderSlots.install missing.adapter}

def configuration {E : Type} (missing : IDa_Deployed.Uninstalled E) (err : E)
 (r : NP6_StdModel.Reservation) :=
 FIp_Install.configuration err (IDa_Deployed.deployedConfiguration (select missing) err r) r

def sdk {E : Type} (missing : IDa_Deployed.Uninstalled E) (err : E)
 (r : NP6_StdModel.Reservation) := DrvC_Installation.sdk (configuration missing err r)

theorem selected {E : Type} (missing : IDa_Deployed.Uninstalled E) (err : E)
 (r : NP6_StdModel.Reservation) :
 (sdk missing err r).op23 = AspisR1.NFY_JHd_RequestNative.decode ∧
 (sdk missing err r).op25 = (NHY_RegistrySlots.install missing.adapter).op25 ∧
 (sdk missing err r).op26 = (NHY_RegistrySlots.install missing.adapter).op26 ∧
 (sdk missing err r).op27 = (NHY_RegistrySlots.install missing.adapter).op27 ∧
 (sdk missing err r).op28 = (NHY_RegistrySlots.install missing.adapter).op28 ∧
 (sdk missing err r).op29 = NIJ_ActiveSlots.op29 ∧
 (sdk missing err r).op30 = NIJ_ActiveSlots.op30 ∧
 (sdk missing err r).op31 = NJQ_Canonical.registry ∧
 (sdk missing err r).op32 = NJQ_Canonical.entry ∧
 (sdk missing err r).op33 = NCX_Install.op33 ∧
 (sdk missing err r).op34 = NCX_Install.op34 ∧
 (sdk missing err r).op48 = NKF_MasterBox.reference ∧
 (sdk missing err r).op49 = NKF_CheckpointBox.reference :=
 ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms selected
end NND_MissingPartial
