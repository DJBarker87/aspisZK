import CurrentCompactTx1ReachabilityV1
import S6DecoderScopedReuseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentCaller.FirstComposition
open AspisR1CurrentCaller

abbrev OldPublic := AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public

def toCurrentAfterstate (x : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=x.next_pair_index, next_root:=x.next_root, next_frontier:=x.next_frontier}

def toCurrentSnapshot (x : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, sequence:=x.sequence, next_pair_index:=x.next_pair_index, current_root:=x.current_root, frontier:=x.frontier}

def toCurrentTransfer (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, recipient_commitment:=x.recipient_commitment, change_commitment:=x.change_commitment}

def toCurrentWithdrawal (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, amount:=x.amount, destination_token_account:=x.destination_token_account, change_commitment:=x.change_commitment}

def toCurrentTransition (x : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=toCurrentSnapshot x.live_snapshot,candidate_afterstate:=toCurrentAfterstate x.candidate_afterstate}

def toCurrentPublic : OldPublic → Public
  | .Transfer p t => .Transfer (toCurrentTransfer p) (toCurrentTransition t)
  | .Withdrawal p t => .Withdrawal (toCurrentWithdrawal p) (toCurrentTransition t)

def toRetainedAfterstate (x : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=x.next_pair_index, next_root:=x.next_root, next_frontier:=x.next_frontier}

def toRetainedSnapshot (x : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, sequence:=x.sequence, next_pair_index:=x.next_pair_index, current_root:=x.current_root, frontier:=x.frontier}

def toRetainedTransfer (x : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, recipient_commitment:=x.recipient_commitment, change_commitment:=x.change_commitment}

def toRetainedWithdrawal (x : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, amount:=x.amount, destination_token_account:=x.destination_token_account, change_commitment:=x.change_commitment}

def toRetainedTransition (x : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=toRetainedSnapshot x.live_snapshot,candidate_afterstate:=toRetainedAfterstate x.candidate_afterstate}

def toRetainedPublic : Public → OldPublic
  | .Transfer p t => .Transfer (toRetainedTransfer p) (toRetainedTransition t)
  | .Withdrawal p t => .Withdrawal (toRetainedWithdrawal p) (toRetainedTransition t)

/-- Every original public field is retained, for both variants. -/
theorem current_retained_roundtrip (p : Public) : toCurrentPublic (toRetainedPublic p)=p := by
  cases p <;> rfl

theorem retained_current_roundtrip (p : OldPublic) : toRetainedPublic (toCurrentPublic p)=p := by
  cases p <;> rfl

def retainedPhase : verifier.Phase → AspisR1PublicPreparation.FirstCaller.Phase
  | .Parsed => .Parsed
  | .Semantic => .Semantic
  | .SemanticPart i => .SemanticPart i
  | .Prepare => .Prepare
  | .CheckpointRead => .CheckpointRead
  | .Merkle i => .Merkle i
  | .Query i => .Query i
  | .QueryPart i j => .QueryPart i j
  | .CheckpointWrite => .CheckpointWrite
  | .Relation => .Relation
  | .Final => .Final

/-- The actual current compact tx1 on the field-preserving public carrier.
The observer map preserves callbacks, not merely acceptance. Release callers
supply None, so the actual source verifier receives None. -/
def currentTx1 (ops : Ops) (D : aspis_core.digest.Digest32 Unit)
    (pub : OldPublic) (bytes proof : Slice U8) (k : Usize) (digest : Unit)
    (obs : Option (AspisR1PublicPreparation.FirstCaller.Phase → Result Unit)) :
    Result (core.result.Result (alloc.vec.Vec U8) verifier.Error) :=
  verifier.candidate.tx1 ops D (toCurrentPublic pub) bytes proof k digest
    (obs.map fun callback => fun phase => callback (retainedPhase phase))

/-- Complete retained first/first_decoded source control, with its tx1 child
now instantiated by the current compact caller, rather than a free callback. -/
def firstCurrent {E : Type} (invalidAccountData : E) (ops : Ops)
    (D : aspis_core.digest.Digest32 Unit) (error : verifier.Error → Result E)
    (bytes proof : Slice U8) (k : Usize) :=
  AspisR1PublicPreparation.RepinS6First.first invalidAccountData
    (currentTx1 ops D) error bytes proof k

/-- One enclosing first success derives its checked decoder, same public and
exact original byte/proof/k arguments, then the same-run compact preparation,
semantic verification, Prepared::new and post-scratch continuation. The old
independent decoder-success, selected-public, child-tx1, selected-View,
semantic-result, preparation-success and scratch witnesses are not premises. -/
theorem first_current_prepared_new {E : Type} (invalidAccountData : E)
    (ops : Ops) (D : aspis_core.digest.Digest32 Unit) (error : verifier.Error → Result E)
    (bytes proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : firstCurrent invalidAccountData ops D error bytes proof k=ok (.Ok out)) :
    ∃ (s : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (prepared : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
        (semantic y1 : Slice U8) (v : verifier.View) (sem : r1_semantic.Verified Unit),
        ops.op5 proof semantic y1=ok (.Ok v) ∧
        ops.op9 D (toCurrentPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))
          v.semantic () none=ok (.Ok sem) ∧
        ops.op8 D sem v () (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
        Tx1Reachability.afterPrepare ops D bytes proof k () none prepared scratch=ok (.Ok out) := by
  obtain ⟨s,pub,hd,hpub,htx⟩ := AspisR1PublicPreparation.RepinS6First.first_success
    invalidAccountData (currentTx1 ops D) error bytes proof k out h
  subst pub
  change verifier.candidate.tx1 ops D
    (toCurrentPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))
    bytes proof k () none=ok (.Ok out) at htx
  obtain ⟨hk,zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,hnew,htail⟩ :=
    Tx1Reachability.tx1_prepared_new ops D
      (toCurrentPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))
      bytes proof k () out htx
  exact ⟨s,hd,hk,zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,hnew,htail⟩

#print axioms current_retained_roundtrip
#print axioms retained_current_roundtrip
#print axioms currentTx1
#print axioms first_current_prepared_new
end AspisR1CurrentCaller.FirstComposition
