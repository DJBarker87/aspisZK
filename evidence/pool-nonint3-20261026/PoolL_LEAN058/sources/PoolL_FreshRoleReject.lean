import PoolL_FreshRoleControl
import PoolL_FreshControl
import PoolL_FreshLengthReject
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_FreshRoleReject
open Aeneas Aeneas.Std Result PoolL_FreshRoleSource PoolL_FreshRoleControl
local instance : DecidableEq Key := Classical.decEq _

theorem occupied (a : Account) (id expected system : Key)
    (bytes : Slice U8) (size : Usize)
    (cp : bytes.val.length = 192 ∨ bytes.val.length = 1768)
    (other : PoolL_LengthOccupied.OtherWidth size.val) :
    PoolL_fresh_role a id expected system false (.Ok bytes) size = ok (.Err (.Custom 1095966773#u32)) := by
  rw [PoolL_FreshRoleControl.control,PoolL_FreshControl.control]
  have bad := PoolL_FreshLengthReject.occupied bytes size cp other
  by_cases ho : a.owner = id <;> by_cases hs : a.owner = system <;>
    by_cases hk : a.key = expected <;> cases he : a.executable <;>
    cases hsig : a.is_signer <;> cases hw : a.is_writable <;>
    simp [PoolM_NativeCancelGuard.thenResult,ho,hs,hk,bad]
#print axioms occupied
end AspisR1.PoolL_FreshRoleReject
end
