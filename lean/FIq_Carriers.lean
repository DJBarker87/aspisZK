import FIq_NativeTypes
import FIp_SemanticArithmetic
set_option autoImplicit false
namespace AspisR1.FIq_Carriers
open Aeneas Aeneas.Std Result

def toTransfer (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : FIq_Native.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 where
  pool := x.pool
  deployment_domain := x.deployment_domain
  anchor_sequence := x.anchor_sequence
  anchor_root := x.anchor_root
  nullifier := x.nullifier
  asset_id := x.asset_id
  recipient_commitment := x.recipient_commitment
  change_commitment := x.change_commitment

def fromTransfer (x : FIq_Native.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 where
  pool := x.pool
  deployment_domain := x.deployment_domain
  anchor_sequence := x.anchor_sequence
  anchor_root := x.anchor_root
  nullifier := x.nullifier
  asset_id := x.asset_id
  recipient_commitment := x.recipient_commitment
  change_commitment := x.change_commitment

theorem transfer_roundtrip (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : fromTransfer (toTransfer x)=x := rfl
#print axioms transfer_roundtrip

def toWithdrawal (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : FIq_Native.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 where
  pool := x.pool
  deployment_domain := x.deployment_domain
  anchor_sequence := x.anchor_sequence
  anchor_root := x.anchor_root
  nullifier := x.nullifier
  asset_id := x.asset_id
  amount := x.amount
  destination_token_account := x.destination_token_account
  change_commitment := x.change_commitment

def fromWithdrawal (x : FIq_Native.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 where
  pool := x.pool
  deployment_domain := x.deployment_domain
  anchor_sequence := x.anchor_sequence
  anchor_root := x.anchor_root
  nullifier := x.nullifier
  asset_id := x.asset_id
  amount := x.amount
  destination_token_account := x.destination_token_account
  change_commitment := x.change_commitment

theorem withdrawal_roundtrip (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : fromWithdrawal (toWithdrawal x)=x := rfl
#print axioms withdrawal_roundtrip

def toSnapshot (x : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : FIq_Native.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 where
  pool := x.pool
  deployment_domain := x.deployment_domain
  sequence := x.sequence
  next_pair_index := x.next_pair_index
  current_root := x.current_root
  frontier := x.frontier

def fromSnapshot (x : FIq_Native.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 where
  pool := x.pool
  deployment_domain := x.deployment_domain
  sequence := x.sequence
  next_pair_index := x.next_pair_index
  current_root := x.current_root
  frontier := x.frontier

theorem snapshot_roundtrip (x : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : fromSnapshot (toSnapshot x)=x := rfl
#print axioms snapshot_roundtrip

def toAfter (x : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : FIq_Native.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 where
  next_pair_index := x.next_pair_index
  next_root := x.next_root
  next_frontier := x.next_frontier

def fromAfter (x : FIq_Native.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 where
  next_pair_index := x.next_pair_index
  next_root := x.next_root
  next_frontier := x.next_frontier

theorem after_roundtrip (x : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : fromAfter (toAfter x)=x := rfl
#print axioms after_roundtrip

def toTransition (x : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : FIq_Native.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 where
  live_snapshot := toSnapshot x.live_snapshot
  candidate_afterstate := toAfter x.candidate_afterstate

def fromTransition (x : FIq_Native.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 where
  live_snapshot := fromSnapshot x.live_snapshot
  candidate_afterstate := fromAfter x.candidate_afterstate

theorem transition_roundtrip (x : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : fromTransition (toTransition x)=x := rfl
#print axioms transition_roundtrip

abbrev Public := AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev NPublic := FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public
def toPublic : Public → NPublic
  | .Transfer p t => .Transfer (toTransfer p) (toTransition t)
  | .Withdrawal p t => .Withdrawal (toWithdrawal p) (toTransition t)
def fromPublic : NPublic → Public
  | .Transfer p t => .Transfer (fromTransfer p) (fromTransition t)
  | .Withdrawal p t => .Withdrawal (fromWithdrawal p) (fromTransition t)
theorem public_roundtrip (x : Public) : fromPublic (toPublic x)=x := by cases x <;> rfl
abbrev MQ := FIp_SemanticArithmetic.MQ
abbrev NQ := FIq_Native.field.QM31
def toQ (x : MQ) : NQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromQ (x : NQ) : MQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def mapArray {T U : Type} {N : Usize} (f : T → U) (a : Array T N) : Array U N :=
  ⟨a.val.map f,by simpa only [List.length_map] using a.property⟩
def toChallenges (c : AspisR1PublicPreparation.r1_wire.Challenges) : FIq_Native.state_only_prefix.r0.Challenges where
  lambda:=toQ c.lambda
  chi:=toQ c.chi
  theta:=toQ c.theta
  zc:=mapArray toQ c.zc
  mu:=toQ c.mu
  eta:=toQ c.eta
theorem q_roundtrip (x : MQ) : fromQ (toQ x)=x := rfl
theorem nq_roundtrip (x : NQ) : toQ (fromQ x)=x := rfl
#print axioms public_roundtrip
#print axioms q_roundtrip
#print axioms nq_roundtrip
end AspisR1.FIq_Carriers
