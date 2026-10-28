-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_NBC_Audit
set_option autoImplicit false
noncomputable section
namespace NBG_Error
open Aeneas Aeneas.Std Result
abbrev E := AdapterRw.aspis_r1_cost_probe.verifier.Error
abbrev P := AdapterRw.solana_program_error.ProgramError

def label : E → String
  | .Parse => "Parse" | .Semantic => "Semantic" | .Transcript => "Transcript"
  | .Relation => "Relation" | .Merkle => "Merkle" | .Query => "Query"
  | .Checkpoint => "Checkpoint" | .Allocation => "Allocation"
def message (error : E) : String := "r1:error:" ++ label error

def run {State : Type} (log : String → State → Result State) (error : E)
    (state : State) : Result (P × State) := do
  let after ← log (message error) state
  let value ← NBC_ReleaseLeaves.errorValue error
  ok (value,after)

/-- Source wrapper has one log transition, preserving its exact resulting
state and returning the same cohort error value. Runtime logging stays trusted. -/
theorem transition {State : Type} (log : String → State → Result State)
    (error : E) (state : State) :
    run log error state =
      match log (message error) state with
      | .ok after => ok (.InvalidInstructionData,after)
      | .fail e => fail e
      | .div => div := by
  cases h : log (message error) state <;>
    simp only [run,h,NBC_ReleaseLeaves.errorValue,bind_tc_ok,bind_tc_fail,bind_tc_div]

#print axioms transition
end NBG_Error
