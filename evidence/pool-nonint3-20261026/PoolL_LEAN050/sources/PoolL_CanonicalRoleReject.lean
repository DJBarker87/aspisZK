import PoolL_CanonicalRoleControl
import PoolL_BorrowFacts
import PoolL_LengthOccupied
import PoolM_NativeCancelReject
set_option autoImplicit false
namespace AspisR1.PoolL_CanonicalRoleReject
open Aeneas Aeneas.Std Result PoolL_CanonicalRoleSource PoolL_CanonicalRoleControl

theorem occupied (a : Account) (id : Key) (bytes : Slice U8)
    (cp : bytes.val.length = 192 ∨ bytes.val.length = 1768) :
    PoolL_canonical_role a id (.Ok bytes) ≠ ok (.Ok ()) := by
  rw [PoolL_CanonicalRoleControl.control,PoolL_BorrowFacts.success]
  have bad := PoolL_LengthOccupied.rejects bytes 1000#usize cp (by
    unfold PoolL_LengthOccupied.OtherWidth
    exact Or.inr (Or.inr (Or.inl rfl)))
  rw [bad]
  intro yes
  have h := (PoolM_NativeCancelReject.then_accepted _ _).mp yes
  cases h.2
#print axioms occupied
end AspisR1.PoolL_CanonicalRoleReject
