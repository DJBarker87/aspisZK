import FIq_Install
import NBX_SlotValues
set_option autoImplicit false
noncomputable section
namespace NBX_DeployedSelection
open Aeneas Aeneas.Std Result AspisR1

/-- Update existing fields of the adopted seed Configuration. In the headline
this seed is IDa_Deployed.seed missing reservation; its adapter is exactly
missing.adapter. No new record/dictionary carrier or law is introduced. -/
def nativeSeed {E : Type} (c : DrvC_Installation.Configuration FIo_Install.W E) :
    DrvC_Installation.Configuration FIo_Install.W E :=
  {c with adapter := NBX_SlotValues.instantiate c.adapter}

/-- The complete adopted installation preserves these exact seven native
candidate functions. Native P6/caller extraction remains a separate obligation;
this theorem checks the FIq/FIp installation path for every adopted seed.
IDa.seed’s adapter projection is the inherited definition, not a headline replay. -/
theorem selected {E : Type} (seed : DrvC_Installation.Configuration FIo_Install.W E) (err : E)
    (r : NP6_StdModel.Reservation) :
    let c := FIp_Install.configuration err
      (FIq_Install.configuration err (nativeSeed seed) r) r
    (DrvC_Installation.sdk c).op15 =
      PoolS2_PolicySource.pool_v1.format.validate_verifier_policy_v1 ∧
    (DrvC_Installation.sdk c).op25 = NBX_SlotValues.op25 ∧
    (DrvC_Installation.sdk c).op26 = NBX_SlotValues.op26 ∧
    (DrvC_Installation.sdk c).op27 = NBX_SlotValues.op27 ∧
    (DrvC_Installation.sdk c).op28 = NBX_SlotValues.op28 ∧
    (DrvC_Installation.sdk c).op29 = NBX_SlotValues.op29 ∧
    (DrvC_Installation.sdk c).op30 = NBX_SlotValues.op30 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms selected
end NBX_DeployedSelection
end
