import PoolL_CanonicalRoleReject
import PoolM_NativeCancelEffects
set_option autoImplicit false
namespace AspisR1.PoolL_CanonicalRoleEffects
open Aeneas Aeneas.Std Result PoolL_CanonicalRoleSource PoolL_CanonicalRoleControl
open PoolM_NativeCancelEffects

theorem occupied_frame {S E V : Type} (a : Account) (id : Key) (bytes : Slice U8)
    (cp : bytes.val.length = 192 ∨ bytes.val.length = 1768)
    (state : S) (prior : List E) (next : S → List E → Outcome S E V) :
    (afterGuard (PoolL_canonical_role a id (.Ok bytes)) state prior next).state = state ∧
    (afterGuard (PoolL_canonical_role a id (.Ok bytes)) state prior next).effects = prior :=
  blocked_frame _ (PoolL_CanonicalRoleReject.occupied a id bytes cp) state prior next

theorem no_suffix {S E V : Type} (a : Account) (id : Key) (bytes : Slice U8)
    (cp : bytes.val.length = 192 ∨ bytes.val.length = 1768)
    (state : S) (prior : List E) (first second : S → List E → Outcome S E V) :
    afterGuard (PoolL_canonical_role a id (.Ok bytes)) state prior first =
      afterGuard (PoolL_canonical_role a id (.Ok bytes)) state prior second :=
  blocked_suffix _ (PoolL_CanonicalRoleReject.occupied a id bytes cp) state prior first second
#print axioms occupied_frame
#print axioms no_suffix
end AspisR1.PoolL_CanonicalRoleEffects
