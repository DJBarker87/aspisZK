import NMS_R2N_RSLError
set_option autoImplicit false
namespace NMS_R2N_RSLPoolCarriers
open Aeneas Aeneas.Std AdapterRw NMS_R2N_RSLScalars
abbrev Accounts := Slice r1_pool_adapter.owned.OwnedAccount

def digest (x : Aeneas.Std.Array U32 8#usize) : RSL.Digest := x.val.map u32

def identity (x : aspis_statement.pool_v1.format.PoolIdentityV1) : RSL.PoolIdentity :=
 ⟨b32 x.pool,b32 x.asset_mint,b32 x.token_program,u32 x.asset_id,b32 x.deployment_domain⟩

def policy (x : aspis_statement.pool_v1.format.VerifierPolicyV1) : RSL.VerifierPolicy :=
 ⟨u8 x.flags,b32 x.registry_program,b32 x.registry_authority,b32 x.policy_binding⟩

def master (x : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) : RSL.Master :=
 ⟨u8 x.bump,identity x.identity,policy x.verifier_policy,u8 x.initialized_lane_mask,
 x.has_checkpoint,u64 x.next_checkpoint_sequence,x.last_checkpoint_lane_sequences.val.map u64⟩

def checkpoint (x : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) : RSL.Checkpoint :=
 ⟨u8 x.bump,b32 x.master,b32 x.deployment_domain,u64 x.checkpoint_sequence,digest x.global_root,
 x.lane_sequences.val.map u64⟩

def tree (x : aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1) : RSL.Tree :=
 ⟨u64 x.next_leaf_index,digest x.root,x.frontier.val.map digest⟩

def lane (x : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1) : RSL.LaneState :=
 ⟨u8 x.bump,b32 x.master,u8 x.lane_id,tree x.tree⟩

def snapshot (x : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : RSL.LiveSnapshot :=
 ⟨b32 x.pool,b32 x.deployment_domain,u64 x.sequence,u64 x.next_pair_index,digest x.current_root,
 x.frontier.val.map digest⟩

/-- Every field of each of the four owned Box payloads is retained. Allocator
addresses are outside the canonical obligation under (bl)(3). -/
def authenticated (x : r1_pool_adapter.AuthenticatedAsq8Accounts) : RSL.Authenticated :=
 ⟨b32 x.master_account,b32 x.checkpoint_account,b32 x.selected_lane_account,
 master x.master,checkpoint x.checkpoint,lane x.selected_lane,snapshot x.live_snapshot⟩

def account (x : r1_pool_adapter.owned.OwnedAccount) : RSL.OwnedAccount :=
 ⟨b32 x.key,b32 x.owner,x.is_signer,x.is_writable,x.executable,
 NMS_R2N_RSLError.reply (fun n : Usize => n.val) x.length,
 NMS_R2N_RSLError.reply (fun v => v.val.map u8) x.bytes⟩

def accounts (x : Accounts) : List RSL.OwnedAccount := x.val.map account

def args233 (p : solana_pubkey.Pubkey) (a : Accounts) (pool : solana_pubkey.Pubkey)
 (lane_ : U8) (slot : U64) : RSL.TX2_233.Args :=
 ⟨b32 p,accounts a,b32 pool,u8 lane_,u64 slot⟩

def args242 (p : solana_pubkey.Pubkey) (a : Accounts) (data : Slice U8)
 (slot : core.result.Result U64 solana_program_error.ProgramError) : RSL.TX2_242.Args :=
 ⟨b32 p,accounts a,bytes data,NMS_R2N_RSLError.reply u64 slot⟩

def args241 (p : solana_pubkey.Pubkey) (a : Accounts) (data : Slice U8)
 (slot : core.result.Result U64 solana_program_error.ProgramError) : RSL.TX2_241.Args :=
 ⟨b32 p,accounts a,bytes data,NMS_R2N_RSLError.reply u64 slot⟩

theorem accounts_length (a : Accounts) : (accounts a).length = a.val.length := List.length_map _

theorem digest_length (x : Aeneas.Std.Array U32 8#usize) : (digest x).length = 8 := by
 simpa [digest] using x.property

theorem tree_frontier_length
 (x : aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1) :
 (tree x).frontier.length = 20 := by simpa [tree] using x.frontier.property

#print axioms accounts_length
#print axioms digest_length
#print axioms tree_frontier_length
end NMS_R2N_RSLPoolCarriers
