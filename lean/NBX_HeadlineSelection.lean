import IDa_Deployed
import NBX_DeployedSelection
set_option autoImplicit false
noncomputable section
namespace NBX_HeadlineSelection
open Aeneas Aeneas.Std Result AspisR1

/-- One existing missing record with its seven demonstrated candidate fields
instantiated. This is not a witness of the complete extraction premise. -/
def nativeMissing {E : Type} (m : IDa_Deployed.Uninstalled E) : IDa_Deployed.Uninstalled E :=
  {m with adapter := NBX_SlotValues.instantiate m.adapter}

theorem seed_instance {E : Type} (m : IDa_Deployed.Uninstalled E)
    (r : NP6_StdModel.Reservation) :
    IDa_Deployed.seed (nativeMissing m) r =
      NBX_DeployedSelection.nativeSeed (IDa_Deployed.seed m r) := rfl

/-- Actual headline missing/seed/configuration chain, retaining the SAME seven
candidate functions. Full native caller/extraction association is not a premise
or conclusion of this field-selection theorem. -/
theorem selected {E : Type} (m : IDa_Deployed.Uninstalled E) (err : E)
    (r : NP6_StdModel.Reservation) :
    let c := FIp_Install.configuration err
      (IDa_Deployed.deployedConfiguration (nativeMissing m) err r) r
    (DrvC_Installation.sdk c).op15 =
      PoolS2_PolicySource.pool_v1.format.validate_verifier_policy_v1 ∧
    (DrvC_Installation.sdk c).op25 = NBX_SlotValues.op25 ∧
    (DrvC_Installation.sdk c).op26 = NBX_SlotValues.op26 ∧
    (DrvC_Installation.sdk c).op27 = NBX_SlotValues.op27 ∧
    (DrvC_Installation.sdk c).op28 = NBX_SlotValues.op28 ∧
    (DrvC_Installation.sdk c).op29 = NBX_SlotValues.op29 ∧
    (DrvC_Installation.sdk c).op30 = NBX_SlotValues.op30 := by
  simpa only [IDa_Deployed.deployedConfiguration,seed_instance] using
    NBX_DeployedSelection.selected (IDa_Deployed.seed m r) err r

/-- Unselected fields of this ONE missing record remain the original fields.
The installed projection for each is checked separately to avoid repeating
large configuration normalization in a single conjunction. -/
theorem remaining_adapter {E : Type} (m : IDa_Deployed.Uninstalled E) :
    (nativeMissing m).adapter.op23 = m.adapter.op23 ∧
    (nativeMissing m).adapter.op31 = m.adapter.op31 ∧
    (nativeMissing m).adapter.op32 = m.adapter.op32 ∧
    (nativeMissing m).adapter.op33 = m.adapter.op33 ∧
    (nativeMissing m).adapter.op34 = m.adapter.op34 ∧
    (nativeMissing m).adapter.op48 = m.adapter.op48 ∧
    (nativeMissing m).adapter.op49 = m.adapter.op49 ∧
    (nativeMissing m).adapter.op53 = m.adapter.op53 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms seed_instance
#print axioms selected
#print axioms remaining_adapter
end NBX_HeadlineSelection
end
