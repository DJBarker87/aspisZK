import NKU_HeaderValue
set_option autoImplicit false
namespace NKU_HeaderSize
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
/-- Small closed parameter arithmetic only:744+16*64, not a recurrence. -/
theorem size : CheckpointBytes4Ops.checkpointSize (NIL_Carriers.variant transport.Variant.S2)=ok 1768#usize := by decide
#print axioms size
end NKU_HeaderSize
