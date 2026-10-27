import PoolL_MarkerRoleControl
import PoolL_MarkerControl
import PoolL_MarkerLengthReject
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_MarkerRoleReject
open Aeneas Aeneas.Std Result PoolL_MarkerRoleSource PoolL_MarkerRoleControl
local instance : DecidableEq Key := Classical.decEq _

theorem occupied (a : Account) (id system : Key)
    (bytes : Slice U8)
    (cp : bytes.val.length = 192 ∨ bytes.val.length = 1768) :
    PoolL_marker_role a id system false (.Ok bytes) = ok (.Err (.Custom 1095966757#u32)) := by
  rw [PoolL_MarkerRoleControl.control,PoolL_MarkerControl.control]
  have bad := PoolL_MarkerLengthReject.occupied bytes cp
  by_cases ho : a.owner = id <;> by_cases hs : a.owner = system <;>
    cases he : a.executable <;>
    cases hsig : a.is_signer <;> cases hw : a.is_writable <;>
    simp [PoolM_NativeCancelGuard.thenResult,ho,hs,bad]
#print axioms occupied
end AspisR1.PoolL_MarkerRoleReject
end
