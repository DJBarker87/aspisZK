import NLM_Entry213Cuts
set_option autoImplicit false
noncomputable section
namespace NLM_Entry213
open Aeneas Aeneas.Std AspisR1 NLM_Process221
/-- Required DRIVER fold of the MODEL schedule, not a native row root. -/
theorem model_fold {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (child : ChildObservation Account Ambient)
 (packet : Packet hashv callee child) (s : State Account Ambient) :
 NGP_L181.NativeAssociation hashv (NLM_Entry213.code callee s) (NLM_Entry213.observation child s) :=
 NHZ_DRIVER.events_from_cuts hashv (NLM_Entry213.code callee s) (NLM_Entry213.code callee s)
  (NLM_Entry213.observation child s) (model_cuts hashv callee child packet s) rfl
#print model_fold
#print axioms model_fold
end NLM_Entry213
