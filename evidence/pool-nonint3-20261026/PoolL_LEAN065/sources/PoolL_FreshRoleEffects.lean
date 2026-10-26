import PoolL_FreshRoleReject
import PoolM_NativeCancelEffects
set_option autoImplicit false
namespace AspisR1.PoolL_FreshRoleEffects
open Aeneas Aeneas.Std Result PoolL_FreshRoleSource PoolL_FreshRoleControl
open PoolM_NativeCancelEffects (Outcome afterGuard blocked_frame blocked_suffix)

theorem occupied_frame {S E V : Type} (a : Account) (id expected system : Key) (bytes : Slice U8) (size : Usize)
    (cp : bytes.val.length = 192 ∨ bytes.val.length = 1768)
    (other : PoolL_LengthOccupied.OtherWidth size.val)
    (state : S) (prior : List E) (next : S → List E → Outcome S E V) :
    afterGuard (PoolL_fresh_role a id expected system false (.Ok bytes) size) state prior next =
      ⟨ok (.Err (.Custom 1095966773#u32)),state,prior⟩ := by
  rw [PoolL_FreshRoleReject.occupied a id expected system bytes size cp other]
  rfl
#print axioms occupied_frame
end AspisR1.PoolL_FreshRoleEffects
