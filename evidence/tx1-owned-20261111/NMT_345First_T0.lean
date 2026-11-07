import NMT_345TransportBase
import NMT_first.Types
set_option autoImplicit false
noncomputable section
namespace NMT_345First
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT0 (x : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : NMT_first.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.amount,x.destination_token_account,x.change_commitment⟩
def fromT0 (x : NMT_first.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.amount,x.destination_token_account,x.change_commitment⟩
@[simp] theorem toT0_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : fromT0 (toT0 x) = x := by
 cases x <;> simp [toT0,fromT0]
#print axioms toT0_inverse
@[simp] theorem fromT0_inverse (x : NMT_first.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : toT0 (fromT0 x) = x := by
 cases x <;> simp [fromT0,toT0]
#print axioms fromT0_inverse
end NMT_345First
