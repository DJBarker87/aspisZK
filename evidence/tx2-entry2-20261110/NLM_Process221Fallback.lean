import NLM_Process221State
set_option autoImplicit false
noncomputable section
namespace NLM_Process221
open Aeneas Aeneas.Std AspisR1 AspisR1.CheckpointBytes5Effect
/-- Both actual stage1 equality occurrences, in source order. -/
def fallback {Account Ambient : Type} (callee : ChildCode Account Ambient)
 (s : State Account Ambient) : Code (Out Ambient) :=
 .step (Hiq_DispatchSource.eqU8 s.frame.data (Array.make 2#usize [3#u8,10#u8])) fun first=>
 if first then callee .first s.frame s.world else
 .step (Hiq_DispatchSource.eqU8 s.frame.data (Array.make 2#usize [3#u8,11#u8])) fun second=>
 if second then callee .first s.frame s.world else callee .second s.frame s.world

def fallbackObservation {Account Ambient : Type} (child : ChildObservation Account Ambient)
 (s : State Account Ambient) : NGP_L181.Observation (Out Ambient) :=
 NLM_CodeStep.select (Hiq_DispatchSource.eqU8 s.frame.data (Array.make 2#usize [3#u8,10#u8])) fun first=>
 if first then child .first s.frame s.world else
 NLM_CodeStep.select (Hiq_DispatchSource.eqU8 s.frame.data (Array.make 2#usize [3#u8,11#u8])) fun second=>
 if second then child .first s.frame s.world else child .second s.frame s.world
#print fallback
end NLM_Process221
