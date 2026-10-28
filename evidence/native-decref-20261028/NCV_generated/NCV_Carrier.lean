import NCV_Reference.Funs
import AdapterRwModel
set_option autoImplicit false
namespace NCV_Carrier
open Aeneas Aeneas.Std Result
open AdapterRw.aspis_statement.pool_v1

def identity (v : NCV_Reference.Identity) : format.PoolIdentityV1 :=
  ⟨v.pool,v.asset_mint,v.token_program,v.asset_id,v.deployment_domain⟩
def policy (v : NCV_Reference.Policy) : format.VerifierPolicyV1 :=
  ⟨v.flags,v.registry_program,v.registry_authority,v.policy_binding⟩
def master (v : NCV_Reference.Master) : pair_forest_accounts.PoolV1PairForestMasterV1 :=
  ⟨v.bump,identity v.identity,policy v.verifier_policy,v.initialized_lane_mask,
    v.has_checkpoint,v.next_checkpoint_sequence,v.last_checkpoint_lane_sequences⟩
def checkpoint (v : NCV_Reference.Checkpoint) : pair_forest_accounts.PoolV1PairForestCheckpointV1 :=
  ⟨v.bump,v.master,v.deployment_domain,v.checkpoint_sequence,v.global_root,v.lane_sequences⟩
def lane (v : NCV_Reference.Lane) : pair_forest_accounts.PoolV1PairForestLaneStateV1 :=
  ⟨v.bump,v.master,v.lane_id,⟨v.next_leaf_index,v.root,v.frontier⟩⟩

def fromIdentity (v : format.PoolIdentityV1) : NCV_Reference.Identity :=
  ⟨v.pool,v.asset_mint,v.token_program,v.asset_id,v.deployment_domain⟩
def fromPolicy (v : format.VerifierPolicyV1) : NCV_Reference.Policy :=
  ⟨v.flags,v.registry_program,v.registry_authority,v.policy_binding⟩
def fromMaster (v : pair_forest_accounts.PoolV1PairForestMasterV1) : NCV_Reference.Master :=
  ⟨v.bump,fromIdentity v.identity,fromPolicy v.verifier_policy,v.initialized_lane_mask,
    v.has_checkpoint,v.next_checkpoint_sequence,v.last_checkpoint_lane_sequences⟩
def fromCheckpoint (v : pair_forest_accounts.PoolV1PairForestCheckpointV1) : NCV_Reference.Checkpoint :=
  ⟨v.bump,v.master,v.deployment_domain,v.checkpoint_sequence,v.global_root,v.lane_sequences⟩
def fromLane (v : pair_forest_accounts.PoolV1PairForestLaneStateV1) : NCV_Reference.Lane :=
  ⟨v.bump,v.master,v.lane_id,v.tree.next_leaf_index,v.tree.root,v.tree.frontier⟩

theorem identity_roundtrip (v : NCV_Reference.Identity) : fromIdentity (identity v)=v := by cases v;rfl
theorem policy_roundtrip (v : NCV_Reference.Policy) : fromPolicy (policy v)=v := by cases v;rfl
theorem master_roundtrip (v : NCV_Reference.Master) : fromMaster (master v)=v := by
  cases v with | mk _ i p _ _ _ _ => cases i;cases p;rfl
theorem checkpoint_roundtrip (v : NCV_Reference.Checkpoint) : fromCheckpoint (checkpoint v)=v := by cases v;rfl
theorem lane_roundtrip (v : NCV_Reference.Lane) : fromLane (lane v)=v := by cases v;rfl

theorem master_surjective (v : pair_forest_accounts.PoolV1PairForestMasterV1) : master (fromMaster v)=v := by
  cases v with | mk _ i p _ _ _ _ => cases i;cases p;rfl
theorem checkpoint_surjective (v : pair_forest_accounts.PoolV1PairForestCheckpointV1) : checkpoint (fromCheckpoint v)=v := by cases v;rfl
theorem lane_surjective (v : pair_forest_accounts.PoolV1PairForestLaneStateV1) : lane (fromLane v)=v := by
  cases v with | mk _ _ _ t => cases t;rfl

#print axioms identity_roundtrip
#print axioms policy_roundtrip
#print axioms master_roundtrip
#print axioms checkpoint_roundtrip
#print axioms lane_roundtrip
#print axioms master_surjective
#print axioms checkpoint_surjective
#print axioms lane_surjective
end NCV_Carrier
