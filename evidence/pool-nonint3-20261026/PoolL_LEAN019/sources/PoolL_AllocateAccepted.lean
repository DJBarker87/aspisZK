import PoolL_AllocateControl
import PoolM_NativeCancelReject
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_AllocateAccepted
open Aeneas Aeneas.Std Result PoolL_AllocateSource PoolL_AllocateControl
local instance : DecidableEq Key := Classical.decEq _

theorem accepted (empty : Account → Result Bool) (system loader : Key)
    (payer a sys : Account) :
    allocatePrefix empty system loader payer a sys = ok (.Ok ()) ↔
      payerSystem system loader payer sys = ok (.Ok ()) ∧
      a.owner = system ∧ empty a = ok true := by
  rw [control,PoolM_NativeCancelReject.then_accepted]
  by_cases owner : a.owner = system
  · cases h : empty a <;> simp [owner] <;> rename_i x
    cases x <;> simp
  · simp [owner]

#print axioms accepted
end AspisR1.PoolL_AllocateAccepted
end
