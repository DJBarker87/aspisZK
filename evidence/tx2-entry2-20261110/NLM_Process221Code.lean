import NLM_Process221DispatchCuts
set_option autoImplicit false
noncomputable section
namespace NLM_Process221
open Aeneas Aeneas.Std AspisR1 AspisR1.CheckpointBytes5Effect
/-- Source order: first().copied(), then dispatch. The original Frame is
passed unchanged to the selected child; only returned child state advances. -/
def code {Account Ambient : Type} (callee : ChildCode Account Ambient)
 (s : State Account Ambient) : Code (Out Ambient) :=
 .step (Hiq_DispatchSource.firstByte s.frame.data) fun head=>
 .step (Hiq_DispatchSource.copied head) fun value=>
 dispatch callee {s with head:=some head} value

def observation {Account Ambient : Type} (child : ChildObservation Account Ambient)
 (s : State Account Ambient) : NGP_L181.Observation (Out Ambient) :=
 NLM_CodeStep.select (Hiq_DispatchSource.firstByte s.frame.data) fun head=>
 NLM_CodeStep.select (Hiq_DispatchSource.copied head) fun value=>
 dispatchObservation child {s with head:=some head} value
#print code
end NLM_Process221
