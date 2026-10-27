import Hiq_DispatchRelease
import GExq_AccountExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DispatchOracle
open Aeneas Aeneas.Std Result Hiq_DispatchSource
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
abbrev Reply := Result (core.result.Result Unit PE)

def program (first second : Program Bytes State Reply) (data : Slice U8) : Program Bytes State Reply :=
  match Hiq_ReleaseRoute.route data with
  | .first => first
  | .second => second
  | .reject => .done (ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidInstructionData))

/-- Rejected source inputs ask nothing, with no restriction on input length. -/
theorem rejected (first second : Program Bytes State Reply) (data : Slice U8)
    (reject : Hiq_ReleaseRoute.route data = .reject) (H : Bytes → State) :
    eval H (program first second data) =
      ([],ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidInstructionData)) := by
  simp only [program,reject,eval]

/-- On each selected child, the complete ordered log is retained verbatim. -/
theorem first_log (first second : Program Bytes State Reply) (data : Slice U8)
    (selected : Hiq_ReleaseRoute.route data = .first) (H : Bytes → State) :
    eval H (program first second data) = eval H first := by simp only [program,selected]

theorem second_log (first second : Program Bytes State Reply) (data : Slice U8)
    (selected : Hiq_ReleaseRoute.route data = .second) (H : Bytes → State) :
    eval H (program first second data) = eval H second := by simp only [program,selected]

/-- Only the reached child interpretation is needed; all failure/divergence
results pass through unchanged. This is an actual source value refinement of
extracted dispatcher, not an assertion that opaque children are implemented. -/
theorem source {Account : Type} (ops : Ops Account) (id : Key) (accounts : Slice Account)
    (first second : Program Bytes State Reply) (data : Slice U8) (H : Bytes → State)
    (one : Hiq_ReleaseRoute.route data = .first → (eval H first).2 = ops.first id accounts data)
    (two : Hiq_ReleaseRoute.route data = .second → (eval H second).2 = ops.second id accounts data) :
    (eval H (program first second data)).2 = process_r1_cost_probe_instruction ops id accounts data := by
  rw [Hiq_DispatchRelease.source]
  cases selected : Hiq_ReleaseRoute.route data with
  | first => simpa only [program,selected] using one selected
  | second => simpa only [program,selected] using two selected
  | reject => simp only [program,selected,eval]

#print axioms rejected
#print axioms first_log
#print axioms second_log
#print axioms source
end AspisR1.Hiq_DispatchOracle
end
