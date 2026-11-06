import NLM_Process221FallbackCuts
set_option autoImplicit false
noncomputable section
namespace NLM_Process221
open Aeneas Aeneas.Std AspisR1 AspisR1.CheckpointBytes5Effect
/-- Unrestricted process retains lifecycle alternatives; none are pruned by
an independently assumed ASQ8 route. -/
def dispatch {Account Ambient : Type} (callee : ChildCode Account Ambient)
 (s : State Account Ambient) (head : Option U8) : Code (Out Ambient) :=
 match head with
 | none => fallback callee s
 | some byte =>
   if byte=4#u8 then callee .init s.frame s.world else
   if byte=5#u8 then callee .write s.frame s.world else
   if byte=6#u8 then callee .finalize s.frame s.world else fallback callee s

def dispatchObservation {Account Ambient : Type} (child : ChildObservation Account Ambient)
 (s : State Account Ambient) (head : Option U8) : NGP_L181.Observation (Out Ambient) :=
 match head with
 | none => fallbackObservation child s
 | some byte =>
   if byte=4#u8 then child .init s.frame s.world else
   if byte=5#u8 then child .write s.frame s.world else
   if byte=6#u8 then child .finalize s.frame s.world else fallbackObservation child s
#print dispatch
end NLM_Process221
