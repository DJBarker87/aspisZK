import PoolL_Physical
import PoolM_NativeCancelReject
set_option autoImplicit false
namespace AspisR1.PoolL_CancelPhysical
open Aeneas Aeneas.Std Result PoolL_Physical

/-- Accepted AENEAS005 role cut separates an occupied checkpoint key from every
selected account, including the refund authority. Parser/count/SDK/runtime and
complete ASPX body interpretation remain separate. -/
theorem accepted_separation (s : Snapshot) (target payer coreKey shardKey system id : Key)
    (hasShard : Bool) (cp : Occupied s target)
    (notSystem : (observe s target).owner ≠ system)
    (accepted : PoolM_NativeCancelSource.PoolM_cancel_roles_native (readLength s) system id
      (observe s payer) (observe s coreKey) (observe s shardKey) hasShard = ok (.Ok ())) :
    target ≠ payer ∧ target ≠ coreKey ∧ (hasShard = true → target ≠ shardKey) := by
  have facts := (PoolM_NativeCancelReject.accepted _ _ _ _ _ _ _).mp accepted
  have lengths := PoolM_NativeCancelReject.lengths _ _ _ _ _ _ _ accepted
  constructor
  · intro same
    subst payer
    exact notSystem facts.2.2.2.1
  constructor
  · intro same
    subst coreKey
    have impossible := PoolM_NativeCancelReject.core_occupied (readLength s) system id
      (observe s payer) (observe s target) (observe s shardKey) hasShard
      (Slice.len (bytes s target)) cp rfl
    exact impossible accepted
  · intro live same
    subst shardKey
    subst hasShard
    exact PoolM_NativeCancelReject.shard_occupied (readLength s) system id
      (observe s payer) (observe s coreKey) (observe s target)
      (Slice.len (bytes s target)) cp rfl accepted
#print axioms accepted_separation
end AspisR1.PoolL_CancelPhysical
