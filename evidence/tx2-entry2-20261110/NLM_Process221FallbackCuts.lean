import NLM_Process221Fallback
set_option autoImplicit false
noncomputable section
namespace NLM_Process221
open Aeneas Aeneas.Std AspisR1

theorem fallback_cuts {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (child : ChildObservation Account Ambient)
 (packet : Packet hashv callee child) (s : State Account Ambient) :
 NHZ_DRIVER.Cuts hashv (fallback callee s) (fallbackObservation child s).result
  (fallbackObservation child s).attempted := by
 unfold fallback fallbackObservation
 apply NLM_CodeStep.cut
 intro first _
 cases first with
 | true => exact packet .first s.frame s.world
 | false =>
   apply NLM_CodeStep.cut
   intro second _
   cases second with
   | true => exact packet .first s.frame s.world
   | false => exact packet .second s.frame s.world
#print fallback_cuts
#print axioms fallback_cuts
end NLM_Process221
