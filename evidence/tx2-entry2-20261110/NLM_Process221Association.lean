import NLM_Process221Cuts
set_option autoImplicit false
noncomputable section
namespace NLM_Process221
open Aeneas Aeneas.Std AspisR1
/-- Source MODEL fold via the required DRIVER. The native/code-ordering and
physical descriptor producer must still be installed; no row root follows. -/
theorem model_fold {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (child : ChildObservation Account Ambient)
 (packet : Packet hashv callee child) (s : State Account Ambient) :
 NGP_L181.NativeAssociation hashv (code callee s) (observation child s) :=
 NHZ_DRIVER.events_from_cuts hashv (code callee s) (code callee s) (observation child s)
  (model_cuts hashv callee child packet s) rfl
#print model_fold
#print axioms model_fold
end NLM_Process221
