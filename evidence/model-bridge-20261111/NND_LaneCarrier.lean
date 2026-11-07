import NND_TreeCarrier
set_option autoImplicit false
namespace NND_Carrier
def lane (x : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1) : RSL.LaneState :=
 { bump := byte x.bump,
   master := key x.master,
   lane_id := byte x.lane_id,
   tree := tree x.tree }
theorem lane_injective : Function.Injective lane := by
 intro x y h
 cases x
 cases y
 simp only [lane,RSL.LaneState.mk.injEq,byte_eq_iff,key_eq_iff,tree_eq_iff] at h
 exact AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1.mk.injEq.mpr h
@[simp] theorem lane_eq_iff (x y : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1) : lane x = lane y ↔ x = y :=
 ⟨fun h => lane_injective h,congrArg lane⟩
#print axioms lane_injective
#print axioms lane_eq_iff
end NND_Carrier
