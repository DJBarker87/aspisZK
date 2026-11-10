import LIBB_AuthCarrier
set_option autoImplicit false
/-! NPP_ A2 (lead decision: funded). Target not yet established.

A computable copy of `LIBB_AuthCarrier.raw a := if h : ∃ r, NND_Carrier.auth r = a then some
(Classical.choose h) else none`, with a kernel-checked `npp_eq`. The inverse `unauth` is field-wise
over the carrier tree (`unkey`, `unbyte`, `unslot`, `unword`, and a generic array inverse); only the
back roundtrip `unauth (auth r) = r` is needed:
* if `auth (unauth a) = a`, both sides are `some _`, equal by `NND_Carrier.auth_injective`;
* otherwise no preimage exists, since `auth r = a` gives `unauth a = r`.
No original definition is changed. -/
namespace NPP_RefineA2
open Aeneas Aeneas.Std AdapterRw NND_Carrier

/-- inverse of `fun x => x.val.map f` on arrays (a fixed default outside the image) -/
def unArr {A B : Type} [Inhabited B] {N : Usize} (g : B → A) (l : List B) : Aeneas.Std.Array A N :=
  if h : (l.map g).length = N.val then ⟨l.map g, h⟩ else ⟨List.replicate N.val (g default), by simp⟩

theorem unArr_back {A B : Type} [Inhabited B] {N : Usize} (f : A → B) (g : B → A)
    (back : ∀ a, g (f a) = a) (x : Aeneas.Std.Array A N) : unArr g (x.val.map f) = x := by
  have hm : (x.val.map f).map g = x.val := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id x.val]
    exact List.map_congr_left (fun a _ => back a)
  unfold unArr
  rw [dif_pos (by rw [hm]; exact x.property)]
  exact Subtype.ext hm

def undigest (d : RSL.Digest) : Aeneas.Std.Array aspis_core.field.M31 8#usize := unArr unword d
theorem undigest_back (x : Aeneas.Std.Array aspis_core.field.M31 8#usize) : undigest (digest x) = x :=
  unArr_back word unword word_back x
def unfrontier (l : List RSL.Digest) : Aeneas.Std.Array (Aeneas.Std.Array aspis_core.field.M31 8#usize) 20#usize :=
  unArr undigest l
theorem unfrontier_back (x : Aeneas.Std.Array (Aeneas.Std.Array aspis_core.field.M31 8#usize) 20#usize) :
    unfrontier (frontier x) = x := unArr_back digest undigest undigest_back x
def unslots (l : List UInt64) : Aeneas.Std.Array U64 8#usize := unArr unslot l
theorem unslots_back (x : Aeneas.Std.Array U64 8#usize) : unslots (slots x) = x :=
  unArr_back slot unslot slot_back x

def unpoolIdentity (x : RSL.PoolIdentity) : aspis_statement.pool_v1.format.PoolIdentityV1 :=
  { pool := unkey x.pool, asset_mint := unkey x.asset_mint, token_program := unkey x.token_program,
    asset_id := unword x.asset_id, deployment_domain := unkey x.deployment_domain }
theorem unpoolIdentity_back (x : aspis_statement.pool_v1.format.PoolIdentityV1) :
    unpoolIdentity (poolIdentity x) = x := by
  cases x; simp [unpoolIdentity, poolIdentity]

def unpolicy (x : RSL.VerifierPolicy) : aspis_statement.pool_v1.format.VerifierPolicyV1 :=
  { flags := unbyte x.flags, registry_program := unkey x.registry_program,
    registry_authority := unkey x.registry_authority, policy_binding := unkey x.policy_binding }
theorem unpolicy_back (x : aspis_statement.pool_v1.format.VerifierPolicyV1) : unpolicy (policy x) = x := by
  cases x; simp [unpolicy, policy]

def unmaster (x : RSL.Master) : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1 :=
  { bump := unbyte x.bump, identity := unpoolIdentity x.identity, verifier_policy := unpolicy x.verifier_policy,
    initialized_lane_mask := unbyte x.initialized_lane_mask, has_checkpoint := x.has_checkpoint,
    next_checkpoint_sequence := unslot x.next_checkpoint_sequence,
    last_checkpoint_lane_sequences := unslots x.last_checkpoint_lane_sequences }
theorem unmaster_back (x : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) :
    unmaster (master x) = x := by
  cases x; simp [unmaster, master, unpoolIdentity_back, unpolicy_back, unslots_back]

def uncheckpoint (x : RSL.Checkpoint) : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1 :=
  { bump := unbyte x.bump, master := unkey x.master, deployment_domain := unkey x.deployment_domain,
    checkpoint_sequence := unslot x.checkpoint_sequence, global_root := undigest x.global_root,
    lane_sequences := unslots x.lane_sequences }
theorem uncheckpoint_back (x : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) :
    uncheckpoint (checkpoint x) = x := by
  cases x; simp [uncheckpoint, checkpoint, undigest_back, unslots_back]

def untree (x : RSL.Tree) : aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1 :=
  { next_leaf_index := unslot x.next_leaf_index, root := undigest x.root, frontier := unfrontier x.frontier }
theorem untree_back (x : aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1) :
    untree (tree x) = x := by
  cases x; simp [untree, tree, undigest_back, unfrontier_back]

def unlane (x : RSL.LaneState) : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1 :=
  { bump := unbyte x.bump, master := unkey x.master, lane_id := unbyte x.lane_id, tree := untree x.tree }
theorem unlane_back (x : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1) :
    unlane (lane x) = x := by
  cases x; simp [unlane, lane, untree_back]

def unlive (x : RSL.LiveSnapshot) : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  { pool := unkey x.pool, deployment_domain := unkey x.deployment_domain, sequence := unslot x.sequence,
    next_pair_index := unslot x.next_pair_index, current_root := undigest x.current_root,
    frontier := unfrontier x.frontier }
theorem unlive_back (x : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    unlive (live x) = x := by
  cases x; simp [unlive, live, undigest_back, unfrontier_back]

def unauth (x : RSL.Authenticated) : r1_pool_adapter.AuthenticatedAsq8Accounts :=
  { master_account := unkey x.master_account, checkpoint_account := unkey x.checkpoint_account,
    selected_lane_account := unkey x.selected_lane_account, master := unmaster x.master,
    checkpoint := uncheckpoint x.checkpoint, selected_lane := unlane x.selected_lane,
    live_snapshot := unlive x.live_snapshot }
theorem unauth_back (x : r1_pool_adapter.AuthenticatedAsq8Accounts) : unauth (auth x) = x := by
  cases x; simp [unauth, auth, unmaster_back, uncheckpoint_back, unlane_back, unlive_back]

end NPP_RefineA2

/-! Structural equality on the RSL authenticated records (standard deriving handler; new
computable instances only), for the image test `auth (unauth a) = a`. -/
deriving instance DecidableEq for RSL.PoolIdentity
deriving instance DecidableEq for RSL.VerifierPolicy
deriving instance DecidableEq for RSL.Master
deriving instance DecidableEq for RSL.Checkpoint
deriving instance DecidableEq for RSL.Tree
deriving instance DecidableEq for RSL.LaneState
deriving instance DecidableEq for RSL.LiveSnapshot
deriving instance DecidableEq for RSL.Authenticated

namespace NPP_C.LIBB_AuthCarrier
open NND_Carrier

def raw (a : RSL.Authenticated) : Option _root_.LIBB_AuthCarrier.Raw :=
  if auth (NPP_RefineA2.unauth a) = a then some (NPP_RefineA2.unauth a) else none

theorem raw.npp_eq : @raw = @_root_.LIBB_AuthCarrier.raw := by
  funext a
  unfold raw _root_.LIBB_AuthCarrier.raw
  by_cases h : auth (NPP_RefineA2.unauth a) = a
  · have ex : ∃ r, auth r = a := ⟨_, h⟩
    rw [if_pos h, dif_pos ex]
    congr 1
    apply NND_Carrier.auth_injective
    rw [h, Classical.choose_spec ex]
  · have ex : ¬ ∃ r, auth r = a := by
      rintro ⟨r, hr⟩
      apply h
      rw [← hr, NPP_RefineA2.unauth_back]
    rw [if_neg h, dif_neg ex]
end NPP_C.LIBB_AuthCarrier

#print axioms NPP_RefineA2.unauth_back
#print axioms NPP_C.LIBB_AuthCarrier.raw.npp_eq
