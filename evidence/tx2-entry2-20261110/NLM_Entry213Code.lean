import NLM_Process221Association
set_option autoImplicit false
noncomputable section
namespace NLM_Entry213
open Aeneas Aeneas.Std AspisR1 AspisR1.CheckpointBytes5Effect NLM_Process221
/-- Actual profile admission precedes every process child. No independent
ASQ8, accepted-child, or successful-entry premise is imposed. -/
def code {Account Ambient : Type} (callee : ChildCode Account Ambient)
 (s : State Account Ambient) : Code (Out Ambient) :=
 .step (Hiq_DispatchSource.pool_route.admitted s.frame.data) fun allowed=>
 if allowed then NLM_Process221.code callee s else .done (.Err .InvalidInstructionData,s.world)

def observation {Account Ambient : Type} (child : ChildObservation Account Ambient)
 (s : State Account Ambient) : NGP_L181.Observation (Out Ambient) :=
 NLM_CodeStep.select (Hiq_DispatchSource.pool_route.admitted s.frame.data) fun allowed=>
 if allowed then NLM_Process221.observation child s else ⟨.ok (.Err .InvalidInstructionData,s.world),[]⟩
#print code
end NLM_Entry213
