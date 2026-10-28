import NBN_AccountCallbackObstruction
set_option autoImplicit false
noncomputable section
namespace NBX_SdkRetention
open Aeneas Aeneas.Std Result AspisR1
/-- Preserve the free request field before specializing the configuration.
Registry/account projections are imported from NBK and are not re-proved. -/
theorem request {F E : Type} (c : DrvC_Installation.Configuration F E) :
    (DrvC_Installation.sdk c).op23 = c.adapter.op23 := rfl
/-- Field retention is not a frame proof for the native emission syscall. -/
theorem emission {F E : Type} (c : DrvC_Installation.Configuration F E) :
    (DrvC_Installation.sdk c).op53 = c.adapter.op53 := rfl
#print axioms request
#print axioms emission
end NBX_SdkRetention
end
