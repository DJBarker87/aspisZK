import NLM_Process221Dispatch
set_option autoImplicit false
noncomputable section
namespace NLM_Process221
open Aeneas Aeneas.Std AspisR1

theorem dispatch_cuts {Account Ambient : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (callee : ChildCode Account Ambient) (child : ChildObservation Account Ambient)
 (packet : Packet hashv callee child) (s : State Account Ambient) (head : Option U8) :
 NHZ_DRIVER.Cuts hashv (dispatch callee s head) (dispatchObservation child s head).result
  (dispatchObservation child s head).attempted := by
 cases head with
 | none => exact fallback_cuts hashv callee child packet s
 | some byte =>
   by_cases four : byte=4#u8
   · simpa only [dispatch,dispatchObservation,if_pos four] using packet .init s.frame s.world
   · by_cases five : byte=5#u8
     · simpa only [dispatch,dispatchObservation,if_neg four,if_pos five] using packet .write s.frame s.world
     · by_cases six : byte=6#u8
       · simpa only [dispatch,dispatchObservation,if_neg four,if_neg five,if_pos six] using packet .finalize s.frame s.world
       · simpa only [dispatch,dispatchObservation,if_neg four,if_neg five,if_neg six] using fallback_cuts hashv callee child packet s
#print dispatch_cuts
#print axioms dispatch_cuts
end NLM_Process221
