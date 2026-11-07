import NND_PolicyCarrier
set_option autoImplicit false
namespace NND_Carrier
def master (x : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) : RSL.Master :=
 { bump := byte x.bump,
   identity := poolIdentity x.identity,
   verifier_policy := policy x.verifier_policy,
   initialized_lane_mask := byte x.initialized_lane_mask,
   has_checkpoint := id x.has_checkpoint,
   next_checkpoint_sequence := slot x.next_checkpoint_sequence,
   last_checkpoint_lane_sequences := slots x.last_checkpoint_lane_sequences }
theorem master_injective : Function.Injective master := by
 intro x y h
 cases x
 cases y
 simp only [master,RSL.Master.mk.injEq,id,byte_eq_iff,policy_eq_iff,poolIdentity_eq_iff,slot_eq_iff,slots_eq_iff] at h
 simpa only [AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1.mk.injEq] using h
@[simp] theorem master_eq_iff (x y : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) : master x = master y ↔ x = y :=
 ⟨fun h => master_injective h,congrArg master⟩
#print axioms master_injective
#print axioms master_eq_iff
end NND_Carrier
