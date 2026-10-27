import PoolL_CloseReject
import PoolM_NativeCancelEffects
set_option autoImplicit false
namespace AspisR1.PoolL_CloseEffects
open Aeneas Aeneas.Std Result PoolL_CloseSource PoolL_CloseControl PoolM_NativeCancelEffects

/-- Full close suffix is unreachable at either occupied checkpoint width.
The supplied state and all prior effects remain in order; this is a leaf cut. -/
theorem occupied_no_close {S E V : Type} (length : Account → Result Usize)
    (a refund : Account) (owner : Key) (size n : Usize)
    (cp : n.val = 192 ∨ n.val = 1768) (plan : size.val = 10000 ∨ size.val = 8504)
    (read : length a = ok n) (state : S) (prior : List E)
    (suffix : S → List E → Outcome S E V) :
    afterGuard (closePrefix length a refund owner size) state prior suffix =
      ⟨ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData),state,prior⟩ := by
  rw [PoolL_CloseReject.occupied length a refund owner size n cp plan read]
  rfl

#print axioms occupied_no_close
end AspisR1.PoolL_CloseEffects
