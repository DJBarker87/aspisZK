import PoolL_Physical
import PoolM_NativePlanGuard
set_option autoImplicit false
namespace AspisR1.PoolL_PhysicalPlan
open Aeneas Aeneas.Std Result PoolL_Physical

theorem excluded (s : Snapshot) (key id : Key) (size : Usize)
    (cp : Occupied s key) (plan : size.val = 10000 ∨ size.val = 8504) :
    PoolM_NativePlanGuard.run (observe s key) id size (readLength s (observe s key)) =
      ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := by
  rw [actual_length]
  apply PoolM_NativePlanGuard.size_error
  intro h
  have eq := congrArg (fun x : Usize => x.val) h
  change (bytes s key).val.length = size.val at eq
  rcases cp with cp | cp <;> rcases plan with plan | plan <;> omega
#print axioms excluded
end AspisR1.PoolL_PhysicalPlan
