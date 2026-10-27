import PoolL_AllocateReject
import PoolM_NativeCancelEffects
set_option autoImplicit false
namespace AspisR1.PoolL_AllocateEffects
open Aeneas Aeneas.Std Result PoolL_AllocateSource PoolL_AllocateControl
open PoolM_NativeCancelEffects (Outcome afterGuard blocked_frame blocked_suffix)

theorem occupied_frame {S E V : Type} (empty : Account → Result Bool) (system loader : Key)
    (payer a sys : Account) (occupied : empty a = ok false)
    (state : S) (prior : List E) (next : S → List E → Outcome S E V) :
    (afterGuard (allocatePrefix empty system loader payer a sys) state prior next).state = state ∧
    (afterGuard (allocatePrefix empty system loader payer a sys) state prior next).effects = prior :=
  blocked_frame _ (PoolL_AllocateReject.nonempty empty system loader payer a sys occupied) state prior next
#print axioms occupied_frame
end AspisR1.PoolL_AllocateEffects
