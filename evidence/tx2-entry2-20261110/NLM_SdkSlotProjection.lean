import RPx_Deployed
set_option autoImplicit false
noncomputable section
namespace NLM_SdkSlotProjection
open Aeneas Aeneas.Std AspisR1
/-- Small symbolic predecessor of the deployed slot audit: keep configuration
fields symbolic, rather than normalize the entire headline installation. -/
theorem clone {F C : Type} (c : DrvC_Installation.Configuration F C) :
 (DrvC_Installation.sdk c).op35=c.adapter.op35 := rfl
#print clone
#print axioms clone
end NLM_SdkSlotProjection
