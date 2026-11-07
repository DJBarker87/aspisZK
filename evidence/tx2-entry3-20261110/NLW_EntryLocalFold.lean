import NLW_ProcessLocalFold
import NLM_Entry213Cuts
set_option autoImplicit false
noncomputable section
namespace NLW_EntryLocalFold
open Aeneas Aeneas.Std AspisR1 NLM_Process221
/-- The process packet is requested only when THIS original instruction is
admitted. No admitted=true, ASQ8 or accepted-child premise is supplied. -/
def Packet {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (child : ChildObservation Account Ambient)
 (s : NLM_Process221.State Account Ambient) : Prop :=
 Hiq_DispatchSource.pool_route.admitted s.frame.data=.ok true →
 NLW_ProcessSelect.LocalPacket hashv callee child s
/-- Source/model repair only; physical admission/descriptors and parent
native cuts are not discharged by this equality. -/
theorem cuts {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (child : ChildObservation Account Ambient)
 (s : NLM_Process221.State Account Ambient) (packet : Packet hashv callee child s) :
 NHZ_DRIVER.Cuts hashv (NLM_Entry213.code callee s)
 (NLM_Entry213.observation child s).result (NLM_Entry213.observation child s).attempted := by
 unfold NLM_Entry213.code NLM_Entry213.observation
 apply NLM_CodeStep.cut
 intro admitted returned
 cases admitted with
 | false => exact .leaf (.done _)
 | true => exact NLW_ProcessLocalFold.cuts hashv callee child s (packet returned)
#print Packet
#print cuts
#print axioms cuts
end NLW_EntryLocalFold
