import NDE_Reference8.Funs
import NDE_LiftBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_PublicBridge
abbrev Address := Array U8 32#usize
abbrev Digest := Array FIq_Native.field.M31 8#usize
abbrev Transition := FIq_Native.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev Private := FIq_Native.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := FIq_Native.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev Semantic := FIq_Native.pool_v1.pair_forest_semantic_terminal.SemanticPublic

def privateInput (p : Private) : NDE_Reference8.PrivateInput Address Digest FIq_Native.field.M31 :=
  ⟨p.pool,p.deployment_domain,p.anchor_root,p.nullifier,p.asset_id,p.recipient_commitment,p.change_commitment⟩
def withdrawalInput (p : Withdrawal) : NDE_Reference8.WithdrawalInput Address Digest FIq_Native.field.M31 :=
  ⟨p.pool,p.deployment_domain,p.anchor_root,p.nullifier,p.asset_id,p.amount,p.change_commitment⟩
def toSemantic (p : NDE_Reference8.PublicRef Address Digest FIq_Native.field.M31 Transition) : Semantic :=
  ⟨if p.withdraw then .Withdrawal else .PrivateTransfer,
    p.pool,p.domain,p.anchor,p.nullifier,p.asset,p.recipient,p.change,p.amount,p.transition⟩

theorem private_public (p : Private) (t : Transition) :
    NDE_LiftBridge.mapResult toSemantic (NDE_Reference8.private_public_ref (privateInput p) t) =
    FIq_Native.pool_v1.pair_forest_semantic_terminal.private_public p t := by
  rfl

theorem withdrawal_public (p : Withdrawal) (t : Transition) :
    NDE_LiftBridge.mapResult toSemantic (NDE_Reference8.withdrawal_public_ref (withdrawalInput p) t) =
    FIq_Native.pool_v1.pair_forest_semantic_terminal.withdrawal_public p t := by
  rfl

#print axioms private_public
#print axioms withdrawal_public
end NDE_PublicBridge
