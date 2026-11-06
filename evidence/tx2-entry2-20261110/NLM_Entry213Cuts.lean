import NLM_Entry213Code
set_option autoImplicit false
noncomputable section
namespace NLM_Entry213
open Aeneas Aeneas.Std AspisR1 NLM_Process221
/-- Conditional MODEL assembly; this does not assert that runtime admission
alone proves the SDK implementation, child bodies or physical descriptor cuts. -/
theorem model_cuts {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (child : ChildObservation Account Ambient)
 (packet : Packet hashv callee child) (s : State Account Ambient) :
 NHZ_DRIVER.Cuts hashv (NLM_Entry213.code callee s) (NLM_Entry213.observation child s).result
  (NLM_Entry213.observation child s).attempted := by
 unfold NLM_Entry213.code NLM_Entry213.observation
 apply NLM_CodeStep.cut
 intro allowed _
 cases allowed with
 | false => exact .leaf (.done _)
 | true => exact NLM_Process221.model_cuts hashv callee child packet s
#print model_cuts
#print axioms model_cuts
end NLM_Entry213
