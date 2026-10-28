import RPz7_DrvC_Installation
import NBH_Audit
set_option autoImplicit false
noncomputable section
namespace NBK_DeployedCallbackSelection
open AspisR1

/-- The coherent installed SDK retains these slots from its input adapter.
This is a selection audit, not a native association or an installation. -/
theorem registry {F E : Type} (c : DrvC_Installation.Configuration F E) :
    (DrvC_Installation.sdk c).op25 = c.adapter.op25 ∧
    (DrvC_Installation.sdk c).op26 = c.adapter.op26 ∧
    (DrvC_Installation.sdk c).op27 = c.adapter.op27 ∧
    (DrvC_Installation.sdk c).op28 = c.adapter.op28 ∧
    (DrvC_Installation.sdk c).op29 = c.adapter.op29 ∧
    (DrvC_Installation.sdk c).op30 = c.adapter.op30 ∧
    (DrvC_Installation.sdk c).op31 = c.adapter.op31 ∧
    (DrvC_Installation.sdk c).op32 = c.adapter.op32 ∧
    (DrvC_Installation.sdk c).op33 = c.adapter.op33 ∧
    (DrvC_Installation.sdk c).op34 = c.adapter.op34 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem policy_accounts {F E : Type} (c : DrvC_Installation.Configuration F E) :
    (DrvC_Installation.sdk c).op15 = c.adapter.op15 ∧
    (DrvC_Installation.sdk c).op48 = c.adapter.op48 ∧
    (DrvC_Installation.sdk c).op49 = c.adapter.op49 := ⟨rfl,rfl,rfl⟩

#print axioms registry
#print axioms policy_accounts
end NBK_DeployedCallbackSelection
