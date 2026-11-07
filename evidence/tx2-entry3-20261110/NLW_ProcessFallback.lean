import NLW_ProcessSelect
set_option autoImplicit false
noncomputable section
namespace NLW_ProcessFallback
open Aeneas Aeneas.Std AspisR1 NLM_Process221
/-- Source-only repair of NLM's overly broad packet. The two equality
occurrences are still executed in order; no lifecycle row is requested. -/
theorem cuts {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (child : ChildObservation Account Ambient)
 (s : NLM_Process221.State Account Ambient)
 (packet : ∀ kind,NLW_ProcessSelect.fallback s.frame.data=.ok kind →
 NHZ_DRIVER.Cuts hashv (callee kind s.frame s.world)
  (child kind s.frame s.world).result (child kind s.frame s.world).attempted) :
 NHZ_DRIVER.Cuts hashv (NLM_Process221.fallback callee s)
 (fallbackObservation child s).result (fallbackObservation child s).attempted := by
 unfold NLM_Process221.fallback fallbackObservation
 apply NLM_CodeStep.cut
 intro first firstCall
 cases first with
 | true =>
   apply packet .first
   simp [NLW_ProcessSelect.fallback,firstCall]
 | false =>
   apply NLM_CodeStep.cut
   intro second secondCall
   cases second with
   | true =>
     apply packet .first
     simp [NLW_ProcessSelect.fallback,firstCall,secondCall]
   | false =>
     apply packet .second
     simp [NLW_ProcessSelect.fallback,firstCall,secondCall]
#print cuts
#print axioms cuts
end NLW_ProcessFallback
