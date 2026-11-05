import NHG_Lengths
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_Semantic
open pool_v1.pair_forest_semantic_terminal

def transferValue (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
 (t : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : SemanticPublic :=
 { variant := .PrivateTransfer, pool := p.pool, deployment_domain := p.deployment_domain,
   anchor := p.anchor_root, nullifier := p.nullifier, asset_id := p.asset_id,
   recipient := some p.recipient_commitment, change := p.change_commitment,
   withdrawal_amount := none, transition := t}

def withdrawalValue (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
 (t : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : SemanticPublic :=
 { variant := .Withdrawal, pool := p.pool, deployment_domain := p.deployment_domain,
   anchor := p.anchor_root, nullifier := p.nullifier, asset_id := p.asset_id,
   recipient := none, change := p.change_commitment,
   withdrawal_amount := some p.amount, transition := t}

theorem transfer (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
 (t : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
 private_public p t=ok (transferValue p t) := rfl

theorem withdrawal (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
 (t : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
 withdrawal_public p t=ok (withdrawalValue p t) := rfl

def value : r0.Public → SemanticPublic
 | .Transfer p t => transferValue p t
 | .Withdrawal p t => withdrawalValue p t

theorem source (p : r0.Public) : p.semantic=ok (value p) := by
 cases p <;> rfl

theorem transition (p : r0.Public) : (value p).transition=
 match p with | .Transfer _ t => t | .Withdrawal _ t => t := by
 cases p <;> rfl

#print axioms transfer
#print axioms withdrawal
#print axioms source
#print axioms transition
end AspisR1.NHG_Semantic
