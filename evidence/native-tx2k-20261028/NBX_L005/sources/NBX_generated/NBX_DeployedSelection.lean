import IDa_Deployed
import NBX_SlotValues
set_option autoImplicit false
noncomputable section
namespace NBX_DeployedSelection
open Aeneas Aeneas.Std Result AspisR1

/-- Instantiate existing fields of ONE existing missing record. No law or new
record/dictionary carrier is introduced. Other fields stay universally free. -/
def nativeMissing {E : Type} (m : IDa_Deployed.Uninstalled E) : IDa_Deployed.Uninstalled E :=
  {m with adapter := NBX_SlotValues.instantiate m.adapter}

/-- The complete adopted installation preserves these exact seven native
candidate functions. Native P6/caller extraction remains a separate obligation;
this theorem discharges the previously inspection-only installation path. -/
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
    (DrvC_Installation.sdk c).op30 = NBX_SlotValues.op30 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Uninstantiated decoder/emission slots remain the SAME missing fields;
selection neither closes them nor constrains their native implementations. -/
theorem remaining {E : Type} (m : IDa_Deployed.Uninstalled E) (err : E)
    (r : NP6_StdModel.Reservation) :
    let c := FIp_Install.configuration err
      (IDa_Deployed.deployedConfiguration (nativeMissing m) err r) r
    (DrvC_Installation.sdk c).op23 = m.adapter.op23 ∧
    (DrvC_Installation.sdk c).op31 = m.adapter.op31 ∧
    (DrvC_Installation.sdk c).op32 = m.adapter.op32 ∧
    (DrvC_Installation.sdk c).op33 = m.adapter.op33 ∧
    (DrvC_Installation.sdk c).op34 = m.adapter.op34 ∧
    (DrvC_Installation.sdk c).op48 = m.adapter.op48 ∧
    (DrvC_Installation.sdk c).op49 = m.adapter.op49 ∧
    (DrvC_Installation.sdk c).op53 = m.adapter.op53 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms selected
#print axioms remaining
end NBX_DeployedSelection
end
