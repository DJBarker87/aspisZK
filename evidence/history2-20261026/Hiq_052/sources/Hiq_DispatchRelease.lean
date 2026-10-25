import Hiq_DispatchAdmitted
import Hiq_DispatchFirst
import Hiq_DispatchSecond
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_DispatchRelease
open Aeneas Aeneas.Std Result Hiq_DispatchSource

/-- Exact total dispatcher, including error, divergence and rejection behavior
of its actual selected child. No child success/byte/output premise occurs. -/
theorem source {Account : Type} (ops : Ops Account) (id : Key) (accounts : Slice Account) (data : Slice U8) :
    process_r1_cost_probe_instruction ops id accounts data =
      match Hiq_ReleaseRoute.route data with
      | .first => ops.first id accounts data
      | .second => ops.second id accounts data
      | .reject => ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidInstructionData) := by
  classical
  rw [process_r1_cost_probe_instruction,Hiq_DispatchAdmitted.exact]
  by_cases first : Hiq_ReleaseRoute.stage1 data
  · rw [Hiq_DispatchFirst.source ops id accounts data first]
    simp [Hiq_ReleaseRoute.route,first]
  by_cases second : Hiq_ReleaseRoute.asq8 data
  · rw [Hiq_DispatchSecond.source ops id accounts data second]
    simp [Hiq_ReleaseRoute.route,first,second]
  · simp [Hiq_ReleaseRoute.route,first,second]

/-- Lifecycle callbacks cannot affect any release result, regardless of their
return value, effects implementation, instruction tails or account inputs. -/
theorem lifecycle_irrelevant {Account : Type} (left right : Ops Account) (id : Key)
    (accounts : Slice Account) (data : Slice U8)
    (first : left.first = right.first) (second : left.second = right.second) :
    process_r1_cost_probe_instruction left id accounts data =
      process_r1_cost_probe_instruction right id accounts data := by
  rw [source,source]
  cases Hiq_ReleaseRoute.route data <;> simp only [first,second]

#print axioms source
#print axioms lifecycle_irrelevant
end AspisR1.Hiq_DispatchRelease
end
