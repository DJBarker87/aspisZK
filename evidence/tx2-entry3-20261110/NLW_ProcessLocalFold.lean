import NLW_ProcessDispatch
set_option autoImplicit false
noncomputable section
namespace NLW_ProcessLocalFold
open Aeneas Aeneas.Std AspisR1 NLM_Process221
/-- Source/model hash fold under ONLY the entered SAME-frame child packet.
This repairs the quantified domain finding; native parent cuts remain open. -/
theorem cuts {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (child : ChildObservation Account Ambient)
 (s : NLM_Process221.State Account Ambient)
 (packet : NLW_ProcessSelect.LocalPacket hashv callee child s) :
 NHZ_DRIVER.Cuts hashv (code callee s) (observation child s).result (observation child s).attempted := by
 unfold code observation
 apply NLM_CodeStep.cut
 intro head firstCall
 apply NLM_CodeStep.cut
 intro value copiedCall
 apply NLW_ProcessDispatch.cuts hashv callee child {s with head:=some head} value
 intro kind selected
 apply packet kind
 simpa [NLW_ProcessSelect.selected,firstCall,copiedCall] using selected
#print cuts
#print axioms cuts
end NLW_ProcessLocalFold
