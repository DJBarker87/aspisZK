import NLM_Process221Code
set_option autoImplicit false
noncomputable section
namespace NLM_Process221
open Aeneas Aeneas.Std AspisR1
/-- Complete conditional hash scheduling at the MODEL level, including all
Rust Err and Aeneas abort branches. Physical native parent cuts and full
SDK/allocator/error frames are not supplied by this theorem. -/
theorem model_cuts {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (child : ChildObservation Account Ambient)
 (packet : Packet hashv callee child) (s : State Account Ambient) :
 NHZ_DRIVER.Cuts hashv (code callee s) (observation child s).result (observation child s).attempted := by
 unfold code observation
 apply NLM_CodeStep.cut
 intro head _
 apply NLM_CodeStep.cut
 intro value _
 exact dispatch_cuts hashv callee child packet {s with head:=some head} value
#print model_cuts
#print axioms model_cuts
end NLM_Process221
