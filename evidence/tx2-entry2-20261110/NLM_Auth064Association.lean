import NLM_Auth064Cuts
set_option autoImplicit false
noncomputable section
namespace NLM_Auth064Association
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes NLM_Auth064 NLM_Auth064Code
/-- Uses the mandated DRIVER.events_from_cuts on the exact composed MODEL
schedule. Code ordering relative to the deployed native function, physical
frame interpretation and the full SDK/allocator packet are still missing;
there is deliberately no positive row-root statement here. -/
theorem model_fold {Ambient H : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (common : ChildCode Ambient H) (child : ChildObservation Ambient H)
 (packet : ∀ f world,NLM_RowSpec_065.Domain f →
   NHZ_DRIVER.Cuts hashv (common f world) (child f world).result (child f world).attempted)
 (s : State Ambient H) :
 NGP_L181.NativeAssociation hashv (code common s) (observation child s) :=
 NHZ_DRIVER.events_from_cuts hashv (code common s) (code common s) (observation child s)
  (NLM_Auth064Cuts.fold hashv common child packet s) rfl
#print model_fold
#print axioms model_fold
end NLM_Auth064Association
