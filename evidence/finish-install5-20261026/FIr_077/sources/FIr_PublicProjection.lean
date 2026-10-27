import FIq_Terminal
set_option autoImplicit false
namespace AspisR1.FIr_PublicProjection
open Aeneas Aeneas.Std Result
open FIq_Carriers
abbrev SemPub := FIq_Native.pool_v1.pair_forest_semantic_terminal.SemanticPublic

theorem transfer
    (pub : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (transition : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (out : SemPub)
    (run : FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
      (toPublic (.Transfer pub transition))=ok out) :
    out.variant=.PrivateTransfer ∧ out.pool=pub.pool ∧ out.deployment_domain=pub.deployment_domain ∧
    out.anchor=pub.anchor_root ∧ out.nullifier=pub.nullifier ∧ out.asset_id=pub.asset_id ∧
    out.recipient=some pub.recipient_commitment ∧ out.change=pub.change_commitment ∧
    out.withdrawal_amount=none ∧ out.transition=toTransition transition := by
  have same := Result.ok.inj run
  cases same
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem withdrawal
    (pub : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (transition : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (out : SemPub)
    (run : FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
      (toPublic (.Withdrawal pub transition))=ok out) :
    out.variant=.Withdrawal ∧ out.pool=pub.pool ∧ out.deployment_domain=pub.deployment_domain ∧
    out.anchor=pub.anchor_root ∧ out.nullifier=pub.nullifier ∧ out.asset_id=pub.asset_id ∧
    out.recipient=none ∧ out.change=pub.change_commitment ∧
    out.withdrawal_amount=some pub.amount ∧ out.transition=toTransition transition := by
  have same := Result.ok.inj run
  cases same
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms transfer
#print axioms withdrawal
end AspisR1.FIr_PublicProjection
