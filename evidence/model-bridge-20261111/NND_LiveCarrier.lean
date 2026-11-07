import NND_LaneCarrier
set_option autoImplicit false
namespace NND_Carrier
def live (x : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : RSL.LiveSnapshot :=
 { pool := key x.pool,
   deployment_domain := key x.deployment_domain,
   sequence := slot x.sequence,
   next_pair_index := slot x.next_pair_index,
   current_root := digest x.current_root,
   frontier := frontier x.frontier }
theorem live_injective : Function.Injective live := by
 intro x y h
 cases x
 cases y
 simp only [live,RSL.LiveSnapshot.mk.injEq,digest_eq_iff,frontier_eq_iff,key_eq_iff,slot_eq_iff] at h
 exact AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1.mk.injEq.mpr h
@[simp] theorem live_eq_iff (x y : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : live x = live y ↔ x = y :=
 ⟨fun h => live_injective h,congrArg live⟩
#print axioms live_injective
#print axioms live_eq_iff
end NND_Carrier
