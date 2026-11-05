import NGJ_VERIFIER_IMPORT
set_option autoImplicit false
noncomputable section
namespace NGL_ErrorModel
open Aeneas Aeneas.Std Result
abbrev E := AdapterRw.aspis_r1_cost_probe.verifier.Error
abbrev PE := AdapterRw.solana_program_error.ProgramError

def label : E → String
  | .Parse => "Parse" | .Semantic => "Semantic" | .Transcript => "Transcript"
  | .Relation => "Relation" | .Merkle => "Merkle" | .Query => "Query"
  | .Checkpoint => "Checkpoint" | .Allocation => "Allocation"
def message (e : E) : String := "r1:error:" ++ label e

def run {State : Type} (log : String → State → Result State) (e : E) (state : State) :
    Result (PE × State) := do
  let after ← log (message e) state
  ok (.InvalidInstructionData, after)

theorem transition {State : Type} (log : String → State → Result State) (e : E) (state : State) :
    run log e state = match log (message e) state with
      | .ok after => .ok (.InvalidInstructionData,after)
      | .fail err => .fail err
      | .div => .div := by
  cases h : log (message e) state <;> simp only [run,h,bind_tc_ok,bind_tc_fail,bind_tc_div]

theorem parse_message : message .Parse = "r1:error:Parse" := rfl

#print axioms transition
#print axioms parse_message
end NGL_ErrorModel
