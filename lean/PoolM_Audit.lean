import PoolM_CancelReach
import PoolM_NativeCancelEffects
/-! Focused axioms audit only. No all-handler frame or native whole-ASPX
source/execution instance is asserted by this import audit. -/
#print axioms PoolM_CancelControl.prepared_cases
#print axioms PoolM_CancelControl.authority_cases
#print axioms PoolM_CancelControl.accepted_roles
#print axioms PoolM_CancelControl.occupied_plans
#print axioms PoolM_CancelControl.occupied_authority
#print axioms PoolM_CancelGuard.prepared_ok
#print axioms PoolM_CancelGuard.prepared_wrong_size
#print axioms PoolM_CancelGuard.authority_ok
#print axioms PoolM_CancelGuard.authority_foreign
#print axioms PoolM_CancelReach.admitted
#print axioms PoolM_CancelReach.authority_reachable
#print axioms PoolM_CancelReach.core_reachable_192
#print axioms PoolM_CancelReach.core_reachable_1768
#print axioms PoolM_CancelReach.shard_reachable_192
#print axioms PoolM_CancelReach.shard_reachable_1768
#print axioms PoolM_CancelReach.absent_shard
#print axioms AspisR1.PoolM_NativeCancelEffects.exact_error
#print axioms AspisR1.PoolM_NativeCancelEffects.exact_failure
#print axioms AspisR1.PoolM_NativeCancelEffects.exact_divergence
#print axioms AspisR1.PoolM_NativeCancelEffects.blocked_frame
#print axioms AspisR1.PoolM_NativeCancelEffects.blocked_suffix
#print axioms AspisR1.PoolM_NativeCancelEffects.core_no_suffix
#print axioms AspisR1.PoolM_NativeCancelEffects.shard_no_suffix
#print axioms AspisR1.PoolM_NativeCancelGuard.prepared_eq
#print axioms AspisR1.PoolM_NativeCancelGuard.native_control
#print axioms AspisR1.PoolM_NativeCancelReject.then_accepted
#print axioms AspisR1.PoolM_NativeCancelReject.accepted
#print axioms AspisR1.PoolM_NativeCancelReject.lengths
#print axioms AspisR1.PoolM_NativeCancelReject.core_occupied
#print axioms AspisR1.PoolM_NativeCancelReject.shard_occupied
#print axioms AspisR1.PoolM_NativeCancelReject.authority_occupied
#print axioms AspisR1.PoolM_NativePlanGuard.key_ne
#print axioms AspisR1.PoolM_NativePlanGuard.owner_error
#print axioms AspisR1.PoolM_NativePlanGuard.metadata_error
#print axioms AspisR1.PoolM_NativePlanGuard.size_error
#print axioms AspisR1.PoolM_NativePlanGuard.accepted
