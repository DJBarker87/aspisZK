import NIS_DigestCarrier
set_option autoImplicit false
namespace NIS_PublicCarrier
open Aeneas Aeneas.Std Result
-- Existing nominal owners only. M31 is the shared U32 representation here;
-- arrays/frontiers are copied symbolically, never enumerated or normalized.
abbrev ATransfer := AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev CTransfer := AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
def toCallerTransfer (p : ATransfer) : CTransfer := ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.recipient_commitment,p.change_commitment⟩
def toAdapterTransfer (p : CTransfer) : ATransfer := ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.recipient_commitment,p.change_commitment⟩
theorem Transfer_adapter (p : ATransfer) : toAdapterTransfer (toCallerTransfer p)=p := by cases p; rfl
#print axioms Transfer_adapter
theorem Transfer_caller (p : CTransfer) : toCallerTransfer (toAdapterTransfer p)=p := by cases p; rfl
#print axioms Transfer_caller
abbrev AWithdrawal := AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev CWithdrawal := AspisR1CurrentCaller.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
def toCallerWithdrawal (p : AWithdrawal) : CWithdrawal := ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.amount,p.destination_token_account,p.change_commitment⟩
def toAdapterWithdrawal (p : CWithdrawal) : AWithdrawal := ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.amount,p.destination_token_account,p.change_commitment⟩
theorem Withdrawal_adapter (p : AWithdrawal) : toAdapterWithdrawal (toCallerWithdrawal p)=p := by cases p; rfl
#print axioms Withdrawal_adapter
theorem Withdrawal_caller (p : CWithdrawal) : toCallerWithdrawal (toAdapterWithdrawal p)=p := by cases p; rfl
#print axioms Withdrawal_caller
abbrev ALive := AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev CLive := AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
def toCallerLive (p : ALive) : CLive := ⟨p.pool,p.deployment_domain,p.sequence,p.next_pair_index,p.current_root,p.frontier⟩
def toAdapterLive (p : CLive) : ALive := ⟨p.pool,p.deployment_domain,p.sequence,p.next_pair_index,p.current_root,p.frontier⟩
theorem Live_adapter (p : ALive) : toAdapterLive (toCallerLive p)=p := by cases p; rfl
#print axioms Live_adapter
theorem Live_caller (p : CLive) : toCallerLive (toAdapterLive p)=p := by cases p; rfl
#print axioms Live_caller
abbrev AAfter := AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev CAfter := AspisR1CurrentCaller.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
def toCallerAfter (p : AAfter) : CAfter := ⟨p.next_pair_index,p.next_root,p.next_frontier⟩
def toAdapterAfter (p : CAfter) : AAfter := ⟨p.next_pair_index,p.next_root,p.next_frontier⟩
theorem After_adapter (p : AAfter) : toAdapterAfter (toCallerAfter p)=p := by cases p; rfl
#print axioms After_adapter
theorem After_caller (p : CAfter) : toCallerAfter (toAdapterAfter p)=p := by cases p; rfl
#print axioms After_caller
abbrev ALate := AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev CLate := AspisR1CurrentCaller.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
def toCallerLate (p : ALate) : CLate := ⟨toCallerLive p.live_snapshot,toCallerAfter p.candidate_afterstate⟩
def toAdapterLate (p : CLate) : ALate := ⟨toAdapterLive p.live_snapshot,toAdapterAfter p.candidate_afterstate⟩
theorem Late_adapter (p : ALate) : toAdapterLate (toCallerLate p)=p := by cases p; rfl
theorem Late_caller (p : CLate) : toCallerLate (toAdapterLate p)=p := by cases p; rfl
abbrev APublic := AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev CPublic := AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
def toCaller : APublic → CPublic
 | .Transfer p late => .Transfer (toCallerTransfer p) (toCallerLate late)
 | .Withdrawal p late => .Withdrawal (toCallerWithdrawal p) (toCallerLate late)
def toAdapter : CPublic → APublic
 | .Transfer p late => .Transfer (toAdapterTransfer p) (toAdapterLate late)
 | .Withdrawal p late => .Withdrawal (toAdapterWithdrawal p) (toAdapterLate late)
theorem public_adapter (p : APublic) : toAdapter (toCaller p)=p := by
 cases p <;> simp only [toAdapter,toCaller,Transfer_adapter,Withdrawal_adapter,Late_adapter]
theorem public_caller (p : CPublic) : toCaller (toAdapter p)=p := by
 cases p <;> simp only [toAdapter,toCaller,Transfer_caller,Withdrawal_caller,Late_caller]
abbrev AE := AdapterRw.aspis_r1_cost_probe.verifier.Error
abbrev CE := AspisR1CurrentCaller.verifier.Error
def errorToCaller : AE → CE
 | .Parse => .Parse
 | .Semantic => .Semantic
 | .Transcript => .Transcript
 | .Relation => .Relation
 | .Merkle => .Merkle
 | .Query => .Query
 | .Checkpoint => .Checkpoint
 | .Allocation => .Allocation
def errorToAdapter : CE → AE
 | .Parse => .Parse
 | .Semantic => .Semantic
 | .Transcript => .Transcript
 | .Relation => .Relation
 | .Merkle => .Merkle
 | .Query => .Query
 | .Checkpoint => .Checkpoint
 | .Allocation => .Allocation
theorem error_adapter (e : AE) : errorToAdapter (errorToCaller e)=e := by cases e <;> rfl
theorem error_caller (e : CE) : errorToCaller (errorToAdapter e)=e := by cases e <;> rfl
def outcomeToAdapter {A : Type} : core.result.Result A CE → core.result.Result A AE
 | .Ok x => .Ok x
 | .Err e => .Err (errorToAdapter e)
def resultToAdapter {A : Type} (reply : Result (core.result.Result A CE)) : Result (core.result.Result A AE) := do
 let r ← reply
 ok (outcomeToAdapter r)
theorem returning {A : Type} (r : core.result.Result A CE) :
 resultToAdapter (ok r)=ok (outcomeToAdapter r) := rfl
theorem aborts {A : Type} (e : Error) :
 resultToAdapter (A:=A) (.fail e)=.fail e ∧ resultToAdapter (A:=A) .div=.div := ⟨rfl,rfl⟩
#print axioms Late_adapter
#print axioms Late_caller
#print axioms public_adapter
#print axioms public_caller
#print axioms error_adapter
#print axioms error_caller
#print axioms returning
#print axioms aborts
end NIS_PublicCarrier
