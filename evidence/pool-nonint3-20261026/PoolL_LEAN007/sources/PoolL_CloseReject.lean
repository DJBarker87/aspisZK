import PoolL_CloseAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_CloseReject
open Aeneas Aeneas.Std Result PoolL_CloseSource PoolL_CloseControl
local instance : DecidableEq Key := Classical.decEq _

/-- Exact size mismatch error, including all earlier metadata rejections. -/
theorem size_error (length : Account → Result Usize) (a refund : Account)
    (owner : Key) (size n : Usize) (wrong : n ≠ size) (read : length a = ok n) :
    closePrefix length a refund owner size =
      ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := by
  rw [control]
  split
  · rfl
  · simp [read,wrong]

/-- Both occupied checkpoint formats are excluded from both actual plan sizes. -/
theorem occupied (length : Account → Result Usize) (a refund : Account)
    (owner : Key) (size n : Usize) (cp : n.val = 192 ∨ n.val = 1768)
    (plan : size.val = 10000 ∨ size.val = 8504) (read : length a = ok n) :
    closePrefix length a refund owner size =
      ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := by
  apply size_error length a refund owner size n _ read
  intro eq
  have vals := congrArg (fun x : Usize => x.val) eq
  rcases cp with cp | cp <;> rcases plan with plan | plan <;> omega

#print axioms size_error
#print axioms occupied
end AspisR1.PoolL_CloseReject
end
