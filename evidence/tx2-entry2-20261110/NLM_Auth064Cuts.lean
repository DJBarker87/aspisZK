import NLM_Auth064Code
set_option autoImplicit false
noncomputable section
namespace NLM_Auth064Cuts
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLM_PacketTypes NLM_Auth064 NLM_Auth064Code
/-- Conditional model fold. Every child use has its domain derived at the
actual parse branch and original1880-byte public carrier. This does not
produce any physical native cut or discharge the OPEN065 packet. -/
theorem fold {Ambient H : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (common : ChildCode Ambient H) (child : ChildObservation Ambient H)
 (packet : ∀ f world,NLM_RowSpec_065.Domain f →
   NHZ_DRIVER.Cuts hashv (common f world) (child f world).result (child f world).attempted)
 (s : State Ambient H) :
 NHZ_DRIVER.Cuts hashv (code common s) (observation child s).result (observation child s).attempted := by
 unfold code observation
 cases parsed : NLE_ParseInstall.parse s.input.proof with
 | fail err => exact .leaf (.stepFail _ _ err rfl)
 | div => exact .leaf (.stepDiv _ _ rfl)
 | ok result =>
   cases result with
   | Err err => exact .leaf (.stepOk _ _ _ rfl _ _ (.done _))
   | Ok variant =>
     apply NHZ_DRIVER.Cuts.leaf
     apply NGQ_Cuts.Trace.stepOk _ _ _ rfl
     apply NGQ_Cuts.Trace.stepOk _ _ () rfl
     exact NHZ_DRIVER.trace (packet _ _ (child_domain s variant parsed))
#print fold
#print axioms fold
end NLM_Auth064Cuts
