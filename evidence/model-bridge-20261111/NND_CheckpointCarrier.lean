import NND_MasterCarrier
set_option autoImplicit false
namespace NND_Carrier
def checkpoint (x : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) : RSL.Checkpoint :=
 { bump := byte x.bump,
   master := key x.master,
   deployment_domain := key x.deployment_domain,
   checkpoint_sequence := slot x.checkpoint_sequence,
   global_root := digest x.global_root,
   lane_sequences := slots x.lane_sequences }
theorem checkpoint_injective : Function.Injective checkpoint := by
 intro x y h
 cases x
 cases y
 simp only [checkpoint,RSL.Checkpoint.mk.injEq,byte_eq_iff,digest_eq_iff,key_eq_iff,slot_eq_iff,slots_eq_iff] at h
 exact AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1.mk.injEq.mpr h
@[simp] theorem checkpoint_eq_iff (x y : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) : checkpoint x = checkpoint y ↔ x = y :=
 ⟨fun h => checkpoint_injective h,congrArg checkpoint⟩
#print axioms checkpoint_injective
#print axioms checkpoint_eq_iff
end NND_Carrier
