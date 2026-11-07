import NLW_ProcessFallback
set_option autoImplicit false
noncomputable section
namespace NLW_ProcessDispatch
open Aeneas Aeneas.Std AspisR1 NLM_Process221
/-- Each branch requests only its own entered child's law at the actual
frame/world. The guard equations are consequences of source dispatch. -/
theorem cuts {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (child : ChildObservation Account Ambient)
 (s : NLM_Process221.State Account Ambient) (head : Option U8)
 (packet : ∀ kind,NLW_ProcessSelect.dispatch s.frame.data head=.ok kind →
 NHZ_DRIVER.Cuts hashv (callee kind s.frame s.world)
  (child kind s.frame s.world).result (child kind s.frame s.world).attempted) :
 NHZ_DRIVER.Cuts hashv (NLM_Process221.dispatch callee s head)
 (dispatchObservation child s head).result (dispatchObservation child s head).attempted := by
 cases head with
 | none =>
   apply NLW_ProcessFallback.cuts hashv callee child s
   exact packet
 | some byte =>
   by_cases four : byte=4#u8
   · simpa only [NLM_Process221.dispatch,dispatchObservation,if_pos four] using
      packet .init (by simp [NLW_ProcessSelect.dispatch,four])
   · by_cases five : byte=5#u8
     · simpa only [NLM_Process221.dispatch,dispatchObservation,if_neg four,if_pos five] using
        packet .write (by simp [NLW_ProcessSelect.dispatch,four,five])
     · by_cases six : byte=6#u8
       · simpa only [NLM_Process221.dispatch,dispatchObservation,if_neg four,if_neg five,if_pos six] using
          packet .finalize (by simp [NLW_ProcessSelect.dispatch,four,five,six])
       · simp only [NLM_Process221.dispatch,dispatchObservation,if_neg four,if_neg five,if_neg six]
         apply NLW_ProcessFallback.cuts hashv callee child s
         intro kind selected
         apply packet kind
         simpa only [NLW_ProcessSelect.dispatch,if_neg four,if_neg five,if_neg six] using selected
#print cuts
#print axioms cuts
end NLW_ProcessDispatch
