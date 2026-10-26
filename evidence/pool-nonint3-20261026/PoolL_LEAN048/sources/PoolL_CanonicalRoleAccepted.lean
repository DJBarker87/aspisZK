import PoolL_CanonicalRoleControl
import PoolL_BorrowFacts
import PoolL_CanonicalAccepted
import PoolM_NativeCancelReject
set_option autoImplicit false
namespace AspisR1.PoolL_CanonicalRoleAccepted
open Aeneas Aeneas.Std Result PoolL_CanonicalRoleSource PoolL_CanonicalRoleControl

theorem accepted (a : Account) (id : Key) (data : core.result.Result (Slice U8) Error) :
    PoolL_canonical_role a id data = ok (.Ok ()) ↔
      a.owner = id ∧ a.executable = false ∧ a.is_writable = true ∧ a.is_signer = false ∧
      ∃ bytes, data = .Ok bytes ∧ bytes.val.length = 1000 := by
  rw [control,PoolM_NativeCancelReject.then_accepted,
    PoolL_CanonicalAccepted.accepted,PoolL_BorrowFacts.accepted]
  simp only [UScalar.val, Nat.cast_ofNat]
  tauto
#print axioms accepted
end AspisR1.PoolL_CanonicalRoleAccepted
