import AdapterRwTypes
import CurrentCompactFirstCompositionV1
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisS6CurrentVerifierCarrier

def toPoolV1PairLiveSnapshotV1 (value : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,sequence:=value.sequence,next_pair_index:=value.next_pair_index,current_root:=value.current_root,frontier:=value.frontier}

def fromPoolV1PairLiveSnapshotV1 (value : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,sequence:=value.sequence,next_pair_index:=value.next_pair_index,current_root:=value.current_root,frontier:=value.frontier}

@[simp] theorem from_toPoolV1PairLiveSnapshotV1 (value : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : fromPoolV1PairLiveSnapshotV1 (toPoolV1PairLiveSnapshotV1 value)=value := by
  cases value <;> simp only [toPoolV1PairLiveSnapshotV1,fromPoolV1PairLiveSnapshotV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairLiveSnapshotV1 (value : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : toPoolV1PairLiveSnapshotV1 (fromPoolV1PairLiveSnapshotV1 value)=value := by
  cases value <;> simp only [toPoolV1PairLiveSnapshotV1,fromPoolV1PairLiveSnapshotV1]
  all_goals rfl

def equivPoolV1PairLiveSnapshotV1 : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 ≃ AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 where
  toFun := toPoolV1PairLiveSnapshotV1
  invFun := fromPoolV1PairLiveSnapshotV1
  left_inv := from_toPoolV1PairLiveSnapshotV1
  right_inv := to_fromPoolV1PairLiveSnapshotV1

#print axioms equivPoolV1PairLiveSnapshotV1

def toPoolV1PairVerifiedAfterstateV1 (value : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=value.next_pair_index,next_root:=value.next_root,next_frontier:=value.next_frontier}

def fromPoolV1PairVerifiedAfterstateV1 (value : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=value.next_pair_index,next_root:=value.next_root,next_frontier:=value.next_frontier}

@[simp] theorem from_toPoolV1PairVerifiedAfterstateV1 (value : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : fromPoolV1PairVerifiedAfterstateV1 (toPoolV1PairVerifiedAfterstateV1 value)=value := by
  cases value <;> simp only [toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLiveSnapshotV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairVerifiedAfterstateV1 (value : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : toPoolV1PairVerifiedAfterstateV1 (fromPoolV1PairVerifiedAfterstateV1 value)=value := by
  cases value <;> simp only [toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLiveSnapshotV1]
  all_goals rfl

def equivPoolV1PairVerifiedAfterstateV1 : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 ≃ AspisR1CurrentCaller.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 where
  toFun := toPoolV1PairVerifiedAfterstateV1
  invFun := fromPoolV1PairVerifiedAfterstateV1
  left_inv := from_toPoolV1PairVerifiedAfterstateV1
  right_inv := to_fromPoolV1PairVerifiedAfterstateV1

#print axioms equivPoolV1PairVerifiedAfterstateV1

def toPoolV1PairLatePublicStatementV1 (value : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=toPoolV1PairLiveSnapshotV1 (value.live_snapshot),candidate_afterstate:=toPoolV1PairVerifiedAfterstateV1 (value.candidate_afterstate)}

def fromPoolV1PairLatePublicStatementV1 (value : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=fromPoolV1PairLiveSnapshotV1 (value.live_snapshot),candidate_afterstate:=fromPoolV1PairVerifiedAfterstateV1 (value.candidate_afterstate)}

@[simp] theorem from_toPoolV1PairLatePublicStatementV1 (value : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : fromPoolV1PairLatePublicStatementV1 (toPoolV1PairLatePublicStatementV1 value)=value := by
  cases value <;> simp only [toPoolV1PairLatePublicStatementV1,fromPoolV1PairLatePublicStatementV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairLatePublicStatementV1 (value : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : toPoolV1PairLatePublicStatementV1 (fromPoolV1PairLatePublicStatementV1 value)=value := by
  cases value <;> simp only [toPoolV1PairLatePublicStatementV1,fromPoolV1PairLatePublicStatementV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1]
  all_goals rfl

def equivPoolV1PairLatePublicStatementV1 : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 ≃ AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 where
  toFun := toPoolV1PairLatePublicStatementV1
  invFun := fromPoolV1PairLatePublicStatementV1
  left_inv := from_toPoolV1PairLatePublicStatementV1
  right_inv := to_fromPoolV1PairLatePublicStatementV1

#print axioms equivPoolV1PairLatePublicStatementV1

def toPoolV1WithdrawalPublicV1 (value : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,amount:=value.amount,destination_token_account:=value.destination_token_account,change_commitment:=value.change_commitment}

def fromPoolV1WithdrawalPublicV1 (value : AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,amount:=value.amount,destination_token_account:=value.destination_token_account,change_commitment:=value.change_commitment}

@[simp] theorem from_toPoolV1WithdrawalPublicV1 (value : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : fromPoolV1WithdrawalPublicV1 (toPoolV1WithdrawalPublicV1 value)=value := by
  cases value <;> simp only [toPoolV1WithdrawalPublicV1,fromPoolV1WithdrawalPublicV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1WithdrawalPublicV1 (value : AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : toPoolV1WithdrawalPublicV1 (fromPoolV1WithdrawalPublicV1 value)=value := by
  cases value <;> simp only [toPoolV1WithdrawalPublicV1,fromPoolV1WithdrawalPublicV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1]
  all_goals rfl

def equivPoolV1WithdrawalPublicV1 : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 ≃ AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 where
  toFun := toPoolV1WithdrawalPublicV1
  invFun := fromPoolV1WithdrawalPublicV1
  left_inv := from_toPoolV1WithdrawalPublicV1
  right_inv := to_fromPoolV1WithdrawalPublicV1

#print axioms equivPoolV1WithdrawalPublicV1

def toPoolV1PrivateTransferPublicV1 (value : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,recipient_commitment:=value.recipient_commitment,change_commitment:=value.change_commitment}

def fromPoolV1PrivateTransferPublicV1 (value : AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,recipient_commitment:=value.recipient_commitment,change_commitment:=value.change_commitment}

@[simp] theorem from_toPoolV1PrivateTransferPublicV1 (value : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : fromPoolV1PrivateTransferPublicV1 (toPoolV1PrivateTransferPublicV1 value)=value := by
  cases value <;> simp only [toPoolV1PrivateTransferPublicV1,fromPoolV1PrivateTransferPublicV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1,from_toPoolV1WithdrawalPublicV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PrivateTransferPublicV1 (value : AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : toPoolV1PrivateTransferPublicV1 (fromPoolV1PrivateTransferPublicV1 value)=value := by
  cases value <;> simp only [toPoolV1PrivateTransferPublicV1,fromPoolV1PrivateTransferPublicV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1,to_fromPoolV1WithdrawalPublicV1]
  all_goals rfl

def equivPoolV1PrivateTransferPublicV1 : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 ≃ AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 where
  toFun := toPoolV1PrivateTransferPublicV1
  invFun := fromPoolV1PrivateTransferPublicV1
  left_inv := from_toPoolV1PrivateTransferPublicV1
  right_inv := to_fromPoolV1PrivateTransferPublicV1

#print axioms equivPoolV1PrivateTransferPublicV1

def toPublic (value : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public :=
  match value with
  | .Transfer x0 x1 => AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer (toPoolV1PrivateTransferPublicV1 (x0)) (toPoolV1PairLatePublicStatementV1 (x1))
  | .Withdrawal x0 x1 => AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal (toPoolV1WithdrawalPublicV1 (x0)) (toPoolV1PairLatePublicStatementV1 (x1))

def fromPublic (value : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public :=
  match value with
  | .Transfer x0 x1 => AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer (fromPoolV1PrivateTransferPublicV1 (x0)) (fromPoolV1PairLatePublicStatementV1 (x1))
  | .Withdrawal x0 x1 => AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal (fromPoolV1WithdrawalPublicV1 (x0)) (fromPoolV1PairLatePublicStatementV1 (x1))

@[simp] theorem from_toPublic (value : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) : fromPublic (toPublic value)=value := by
  cases value <;> simp only [toPublic,fromPublic,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1,from_toPoolV1WithdrawalPublicV1,from_toPoolV1PrivateTransferPublicV1]
  all_goals rfl

@[simp] theorem to_fromPublic (value : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) : toPublic (fromPublic value)=value := by
  cases value <;> simp only [toPublic,fromPublic,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1,to_fromPoolV1WithdrawalPublicV1,to_fromPoolV1PrivateTransferPublicV1]
  all_goals rfl

def equivPublic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public ≃ AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public where
  toFun := toPublic
  invFun := fromPublic
  left_inv := from_toPublic
  right_inv := to_fromPublic

#print axioms equivPublic

def toError (value : AdapterRw.aspis_r1_cost_probe.verifier.Error) : AspisR1CurrentCaller.verifier.Error :=
  match value with
  | .Parse => AspisR1CurrentCaller.verifier.Error.Parse
  | .Semantic => AspisR1CurrentCaller.verifier.Error.Semantic
  | .Transcript => AspisR1CurrentCaller.verifier.Error.Transcript
  | .Relation => AspisR1CurrentCaller.verifier.Error.Relation
  | .Merkle => AspisR1CurrentCaller.verifier.Error.Merkle
  | .Query => AspisR1CurrentCaller.verifier.Error.Query
  | .Checkpoint => AspisR1CurrentCaller.verifier.Error.Checkpoint
  | .Allocation => AspisR1CurrentCaller.verifier.Error.Allocation

def fromError (value : AspisR1CurrentCaller.verifier.Error) : AdapterRw.aspis_r1_cost_probe.verifier.Error :=
  match value with
  | .Parse => AdapterRw.aspis_r1_cost_probe.verifier.Error.Parse
  | .Semantic => AdapterRw.aspis_r1_cost_probe.verifier.Error.Semantic
  | .Transcript => AdapterRw.aspis_r1_cost_probe.verifier.Error.Transcript
  | .Relation => AdapterRw.aspis_r1_cost_probe.verifier.Error.Relation
  | .Merkle => AdapterRw.aspis_r1_cost_probe.verifier.Error.Merkle
  | .Query => AdapterRw.aspis_r1_cost_probe.verifier.Error.Query
  | .Checkpoint => AdapterRw.aspis_r1_cost_probe.verifier.Error.Checkpoint
  | .Allocation => AdapterRw.aspis_r1_cost_probe.verifier.Error.Allocation

@[simp] theorem from_toError (value : AdapterRw.aspis_r1_cost_probe.verifier.Error) : fromError (toError value)=value := by
  cases value <;> simp only [toError,fromError,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1,from_toPoolV1WithdrawalPublicV1,from_toPoolV1PrivateTransferPublicV1,from_toPublic]
  all_goals rfl

@[simp] theorem to_fromError (value : AspisR1CurrentCaller.verifier.Error) : toError (fromError value)=value := by
  cases value <;> simp only [toError,fromError,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1,to_fromPoolV1WithdrawalPublicV1,to_fromPoolV1PrivateTransferPublicV1,to_fromPublic]
  all_goals rfl

def equivError : AdapterRw.aspis_r1_cost_probe.verifier.Error ≃ AspisR1CurrentCaller.verifier.Error where
  toFun := toError
  invFun := fromError
  left_inv := from_toError
  right_inv := to_fromError

#print axioms equivError

def toPhase (value : AdapterRw.aspis_r1_cost_probe.verifier.Phase) : AspisR1CurrentCaller.verifier.Phase :=
  match value with
  | .Parsed => AspisR1CurrentCaller.verifier.Phase.Parsed
  | .Semantic => AspisR1CurrentCaller.verifier.Phase.Semantic
  | .SemanticPart x0 => AspisR1CurrentCaller.verifier.Phase.SemanticPart (x0)
  | .Prepare => AspisR1CurrentCaller.verifier.Phase.Prepare
  | .CheckpointRead => AspisR1CurrentCaller.verifier.Phase.CheckpointRead
  | .Merkle x0 => AspisR1CurrentCaller.verifier.Phase.Merkle (x0)
  | .Query x0 => AspisR1CurrentCaller.verifier.Phase.Query (x0)
  | .QueryPart x0 x1 => AspisR1CurrentCaller.verifier.Phase.QueryPart (x0) (x1)
  | .CheckpointWrite => AspisR1CurrentCaller.verifier.Phase.CheckpointWrite
  | .Relation => AspisR1CurrentCaller.verifier.Phase.Relation
  | .Final => AspisR1CurrentCaller.verifier.Phase.Final

def fromPhase (value : AspisR1CurrentCaller.verifier.Phase) : AdapterRw.aspis_r1_cost_probe.verifier.Phase :=
  match value with
  | .Parsed => AdapterRw.aspis_r1_cost_probe.verifier.Phase.Parsed
  | .Semantic => AdapterRw.aspis_r1_cost_probe.verifier.Phase.Semantic
  | .SemanticPart x0 => AdapterRw.aspis_r1_cost_probe.verifier.Phase.SemanticPart (x0)
  | .Prepare => AdapterRw.aspis_r1_cost_probe.verifier.Phase.Prepare
  | .CheckpointRead => AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointRead
  | .Merkle x0 => AdapterRw.aspis_r1_cost_probe.verifier.Phase.Merkle (x0)
  | .Query x0 => AdapterRw.aspis_r1_cost_probe.verifier.Phase.Query (x0)
  | .QueryPart x0 x1 => AdapterRw.aspis_r1_cost_probe.verifier.Phase.QueryPart (x0) (x1)
  | .CheckpointWrite => AdapterRw.aspis_r1_cost_probe.verifier.Phase.CheckpointWrite
  | .Relation => AdapterRw.aspis_r1_cost_probe.verifier.Phase.Relation
  | .Final => AdapterRw.aspis_r1_cost_probe.verifier.Phase.Final

@[simp] theorem from_toPhase (value : AdapterRw.aspis_r1_cost_probe.verifier.Phase) : fromPhase (toPhase value)=value := by
  cases value <;> simp only [toPhase,fromPhase,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1,from_toPoolV1WithdrawalPublicV1,from_toPoolV1PrivateTransferPublicV1,from_toPublic,from_toError]
  all_goals rfl

@[simp] theorem to_fromPhase (value : AspisR1CurrentCaller.verifier.Phase) : toPhase (fromPhase value)=value := by
  cases value <;> simp only [toPhase,fromPhase,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1,to_fromPoolV1WithdrawalPublicV1,to_fromPoolV1PrivateTransferPublicV1,to_fromPublic,to_fromError]
  all_goals rfl

def equivPhase : AdapterRw.aspis_r1_cost_probe.verifier.Phase ≃ AspisR1CurrentCaller.verifier.Phase where
  toFun := toPhase
  invFun := fromPhase
  left_inv := from_toPhase
  right_inv := to_fromPhase

#print axioms equivPhase

end AspisS6CurrentVerifierCarrier
