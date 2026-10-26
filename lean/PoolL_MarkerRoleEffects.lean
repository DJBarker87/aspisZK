import PoolL_MarkerRoleReject
import PoolM_NativeCancelEffects
set_option autoImplicit false
namespace AspisR1.PoolL_MarkerRoleEffects
open Aeneas Aeneas.Std Result PoolL_MarkerRoleSource PoolL_MarkerRoleControl
open PoolM_NativeCancelEffects (Outcome afterGuard blocked_frame blocked_suffix)

theorem occupied_frame {S E V : Type} (a : Account) (id system : Key) (bytes : Slice U8)
    (cp : bytes.val.length = 192 ∨ bytes.val.length = 1768)
    (state : S) (prior : List E) (next : S → List E → Outcome S E V) :
    afterGuard (PoolL_marker_role a id system false (.Ok bytes)) state prior next =
      ⟨ok (.Err (.Custom 1095966757#u32)),state,prior⟩ := by
  rw [PoolL_MarkerRoleReject.occupied a id system bytes cp]
  rfl
#print axioms occupied_frame
end AspisR1.PoolL_MarkerRoleEffects
