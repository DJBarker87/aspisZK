import PoolL_AllocateAccepted
set_option autoImplicit false
namespace AspisR1.PoolL_AllocateReject
open Aeneas Aeneas.Std Result PoolL_AllocateSource PoolL_AllocateControl

theorem non_system (empty : Account → Result Bool) (system loader : Key)
    (payer a sys : Account) (owner : a.owner ≠ system) :
    allocatePrefix empty system loader payer a sys ≠ ok (.Ok ()) := by
  intro h
  exact owner ((PoolL_AllocateAccepted.accepted empty system loader payer a sys).mp h).2.1

theorem nonempty (empty : Account → Result Bool) (system loader : Key)
    (payer a sys : Account) (occupied : empty a = ok false) :
    allocatePrefix empty system loader payer a sys ≠ ok (.Ok ()) := by
  intro h
  have yes := ((PoolL_AllocateAccepted.accepted empty system loader payer a sys).mp h).2.2
  rw [occupied] at yes
  cases yes
#print axioms non_system
#print axioms nonempty
end AspisR1.PoolL_AllocateReject
